"use strict";
const {test}=require("node:test"), assert=require("node:assert/strict");
const fs=require("node:fs"), path=require("node:path"), vm=require("node:vm");
const {createHash,webcrypto}=require("node:crypto");
const {MessageChannel}=require("node:worker_threads");
const template=fs.readFileSync(path.join(__dirname,"../../webapp/service-worker.js"),"utf8");
const scope="https://example.test/duplotrain/";
const clean=x=>JSON.parse(JSON.stringify(x));
function cacheStorage(){
  const map=new Map();let failedPut=false;
  return {map,failPut(value=true){failedPut=value;},async keys(){return [...map.keys()];},
    async has(key){return map.has(key);},
    async delete(key){return map.delete(key);},async open(key){
      if(!map.has(key))map.set(key,new Map());const store=map.get(key);
      const name=k=>typeof k==="string"?k:k.url;
      // Model stored bytes, not long-lived tee streams in Node's Response.clone.
      return {async match(k){const value=store.get(name(k));return value?
        new Response(value.body.slice(0),{status:value.status,headers:value.headers}):undefined;},async put(k,v){
        if(failedPut)throw new DOMException("quota exceeded","QuotaExceededError");store.set(name(k),{
          body:await v.arrayBuffer(),status:v.status,headers:[...v.headers]});},
        async delete(k){return store.delete(name(k));}};
    }};
}
function worker({build="aaa",caches=cacheStorage(),bad=null,now=()=>Date.now(),page="",
  timers={setTimeout,clearTimeout,setInterval,clearInterval},stream=null,clients=async()=>[]}={}){
  const assets=[{url:"index.html",body:`<html>build ${build}${page}</html>`},
    {url:`editor.js?v=${build}`,body:`const build='${build}'`},
    {url:`worker.js?v=${build}`,body:`const engine='${build}'`}];
  const manifest=assets.map(a=>({url:a.url,bytes:Buffer.byteLength(a.body),
    sha256:createHash("sha256").update(a.body).digest("hex")}));
  const version=createHash("sha256").update(JSON.stringify(manifest)).digest("hex").slice(0,16);
  const handlers={},calls=[];let offline=false,activated=0;
  const fetch=async(req,init)=>{
    const url=typeof req==="string"?req:req.url;calls.push(url);
    if(offline||bad==="network")throw new Error("offline");
    const asset=assets.find(a=>new URL(a.url,scope).href===url);
    if(stream&&asset)return new Response(stream(asset,init.signal),{headers:{"Content-Type":"text/html"}});
    const body=bad===asset?.url?"corrupt":bad==="long"&&asset?asset.body+" and more":
      // One byte changed, length kept: only the SHA-256 comparison can catch it.
      bad==="same-length"&&asset?.url.startsWith("editor.js")?asset.body.slice(0,-1)+"x":
      asset?.body||"network fallback";
    return new Response(body,{headers:{"Content-Type":asset?.url==="index.html"?"text/html":"application/javascript",
      "Content-Security-Policy":"default-src 'self'","Content-Encoding":"gzip"}});
  };
  const ctx=vm.createContext({URL,Response,Request,Headers,Uint8Array,ArrayBuffer,AbortController,
    crypto:webcrypto,caches,fetch,MessageChannel,...timers,Date:{now},
    self:{registration:{scope},clients:{claim:async()=>{},matchAll:clients},skipWaiting:async()=>{activated++;},
      addEventListener:(name,fn)=>{handlers[name]=fn;}}});
  vm.runInContext(template.replaceAll("__BUILD__",build).replace("__VERSION__",version)
    .replace("__ASSETS__",JSON.stringify(manifest)),ctx);
  const run=code=>vm.runInContext(code,ctx);
  return {ctx,run,caches,assets,manifest,handlers,calls,setOffline:v=>{offline=v;},setBad:v=>{bad=v;},
    activated:()=>activated,
    async install(){let promise;handlers.install({waitUntil:p=>{promise=p;}});return promise;},
    async activate(){let promise;handlers.activate({waitUntil:p=>{promise=p;}});return promise;},
    async message(type){let promise,result;handlers.message({data:{type},ports:[{postMessage:r=>{result=r;}}],waitUntil:p=>{promise=p;}});
      await promise;return clean(result);},
    async request(url,mode="cors",method="GET"){
      let promise;handlers.fetch({request:{url:new URL(url,scope).href,mode,method},respondWith:p=>{promise=p;}});
      return promise?promise:null;}};
}

test("offline is ready only after every exact asset is verified and marker committed",async()=>{
  const w=worker();assert.equal((await w.ctx.offlineStatus()).ready,false);
  await w.install();assert.equal((await w.ctx.offlineStatus()).ready,true);
  assert.equal(w.calls.length,w.assets.length);assert.equal(w.activated(),0);
  const response=await w.request("index.html","navigate");assert.match(await response.text(),/aaa/);
  assert.equal(response.headers.get("Content-Security-Policy"),"default-src 'self'");
  assert.equal(response.headers.get("Content-Encoding"),null);
  assert.equal(response.headers.get("Content-Length"),String(Buffer.byteLength(w.assets[0].body)));
  w.setOffline(true);assert.match(await (await w.request("./","navigate")).text(),/aaa/);
  assert.match(await (await w.request("editor.js?v=aaa")).text(),/aaa/);
});

for(const bad of ["index.html","editor.js?v=bbb","network","long"])test(`failed version ${bad} preserves verified old version and unrelated caches`,async()=>{
  const caches=cacheStorage(),old=worker({caches});await old.install();
  const other=await caches.open("other-app");await other.put("https://example.test/other",new Response("do not delete"));
  const next=worker({build:"bbb",caches,bad});await assert.rejects(next.install(),/offline|verification/);
  assert.equal((await next.ctx.offlineStatus()).ready,false);
  assert.equal((await old.ctx.offlineStatus()).ready,true);
  assert.ok(caches.map.has("other-app"));assert.equal(next.activated(),0);
  // Only verified files stay, for the next attempt to resume from.
  for(const [url,entry] of caches.map.get(next.run("CACHE"))){
    const asset=next.assets.find(a=>new URL(a.url,scope).href===url);
    if(asset)assert.equal(Buffer.from(entry.body).toString(),asset.body);
  }
});

test("an interrupted installation resumes with the files it already verified",async()=>{
  const w=worker({bad:"worker.js?v=aaa"});
  await assert.rejects(w.install(),/verification failed: worker\.js/);
  assert.equal(w.calls.length,3);
  w.setBad(null);w.calls.length=0;
  assert.equal((await w.install()).ready,true);
  assert.deepEqual(w.calls,[new URL("worker.js?v=aaa",scope).href]);
});

test("a corrupt asset of exactly the promised size fails its SHA-256 check",async()=>{
  const caches=cacheStorage(),old=worker({caches});await old.install();
  const next=worker({build:"bbb",caches,bad:"same-length"});
  // The served bytes match the manifest's length, so the length check alone would accept them.
  const served=await (await next.ctx.fetch(new URL(next.assets[1].url,scope).href,{})).text();
  assert.equal(Buffer.byteLength(served),next.manifest[1].bytes);assert.notEqual(served,next.assets[1].body);
  await assert.rejects(next.install(),/verification failed: editor\.js\?v=bbb/);
  assert.equal((await next.ctx.offlineStatus()).ready,false);
  assert.ok(!caches.map.get(next.run("CACHE")).has(new URL(next.assets[1].url,scope).href));
  assert.equal((await old.ctx.offlineStatus()).ready,true);
});

test("quota failure cannot mark a partial installation ready",async()=>{
  const w=worker();w.caches.failPut();await assert.rejects(w.install(),/quota/);
  assert.equal((await w.ctx.offlineStatus()).ready,false);
  assert.ok(!w.caches.map.has(w.run("CACHE")));  // out of space, the partial version gives it back
  const reply=await w.message("ACTIVATE");assert.equal(reply.ready,false);assert.match(reply.error,/incomplete/);
  assert.equal(w.activated(),0);
});

test("offline update preserves old exact URLs without mixing version query strings",async()=>{
  const caches=cacheStorage(),a=worker({caches}),b=worker({build:"bbb",caches});
  await a.install();await b.install();b.setOffline(true);
  assert.match(await (await b.request("editor.js?v=aaa")).text(),/aaa/);
  assert.match(await (await b.request("editor.js?v=bbb")).text(),/bbb/);
  assert.match(await (await b.request("./","navigate")).text(),/bbb/);
  await assert.rejects(b.request("editor.js?v=unknown"),/offline/);
  const reply=await b.message("ACTIVATE");assert.equal(reply.activated,true);assert.equal(b.activated(),1);
  assert.equal((await a.ctx.offlineStatus()).ready,true);
});

test("evicted assets clear ready status and verified reinstall repairs them",async()=>{
  const w=worker();await w.install();const cache=await w.caches.open(w.run("CACHE"));
  await cache.delete(new URL(w.assets[1].url,scope).href);
  assert.equal((await w.ctx.offlineStatus()).ready,false);
  w.setOffline(true);await assert.rejects(w.request("./","navigate"),/offline/);
  w.setOffline(false);await w.ctx.installVersion();assert.equal((await w.ctx.offlineStatus()).ready,true);
});

test("simultaneous installation messages share one download transaction",async()=>{
  const w=worker();const result=await Promise.all([w.ctx.installVersion(),w.ctx.installVersion()]);
  assert.ok(result.every(r=>r.ready));assert.equal(w.calls.length,w.assets.length);
});

for(const [url,method]of[["api/state","GET"],["api/search/tick","POST"],["service-worker.js","GET"],
  ["https://elsewhere.test/duplotrain/index.html","GET"],["../other/app.js","GET"]]){
  test(`offline worker never intercepts ${method} ${url}`,async()=>{
    const w=worker();await w.install();assert.equal(await w.request(url,"cors",method),null);
  });
}

test("unknown navigation is not silently replaced with the editor",async()=>{
  const w=worker();await w.install();assert.equal(await (await w.request("unknown.html","navigate")).text(),"network fallback");
});

test("activation keeps this and the newest older version, never unrelated or unfinished caches",async()=>{
  const caches=cacheStorage();let clock=1000;const now=()=>clock++;
  const other=await caches.open("other-app");await other.put("https://example.test/other",new Response("keep"));
  const versions=[];
  for(const build of ["aaa","bbb","ccc"]){const w=worker({build,caches,now});await w.install();versions.push(w);}
  const partial=worker({build:"ddd",caches,now}),installing=await caches.open(partial.run("CACHE"));
  await installing.put(new URL("index.html",scope).href,new Response("still installing"));
  await installing.put(partial.run("progressOf(VERSION)"),new Response("",{headers:{"X-Progress":String(clock)}}));
  await versions[2].activate();
  const kept=[...caches.map.keys()];
  assert.ok(kept.includes("other-app")&&kept.includes(partial.run("CACHE")));
  assert.ok(kept.includes(versions[2].run("CACHE"))&&kept.includes(versions[1].run("CACHE")));
  assert.ok(!kept.includes(versions[0].run("CACHE")));
  // Tabs still running the previous version keep its exact assets offline.
  versions[2].setOffline(true);
  assert.match(await (await versions[2].request("editor.js?v=bbb")).text(),/bbb/);
});

test("activation keeps the previously active version, not a superseded waiting update",async()=>{
  const caches=cacheStorage();let clock=1000;const now=()=>clock++;
  const a=worker({build:"aaa",caches,now});await a.install();await a.activate();  // tabs run aaa
  const b=worker({build:"bbb",caches,now});await b.install();                      // waits, never applied
  const c=worker({build:"ccc",caches,now});await c.install();await c.activate();   // ccc applied
  const kept=[...caches.map.keys()];
  assert.ok(kept.includes(a.run("CACHE"))&&kept.includes(c.run("CACHE")));
  assert.ok(!kept.includes(b.run("CACHE")));
  c.setOffline(true);
  assert.match(await (await c.request("editor.js?v=aaa")).text(),/aaa/);
});


test("a changed page under an unchanged build stamp installs as a new version",async()=>{
  const caches=cacheStorage(),a=worker({caches});await a.install();await a.activate();
  // Say the page's CSP changed, which the stamp of the editor and engine sources misses.
  const b=worker({caches,page:" with a new policy"});
  assert.equal(b.run("BUILD"),a.run("BUILD"));assert.notEqual(b.run("CACHE"),a.run("CACHE"));
  assert.equal((await b.ctx.offlineStatus()).ready,false);
  await b.install();assert.equal(b.calls.length,b.assets.length);
  b.setOffline(true);assert.match(await (await b.request("./","navigate")).text(),/new policy/);
  assert.equal((await a.ctx.offlineStatus()).ready,true);
});

// Timers the test advances, and bodies that arrive when the test sends them.
function clock(){
  let now=0,next=0;const timers=new Map();
  const every=(id,fn,ms)=>timers.set(id,{fn:()=>{every(id,fn,ms);fn();},at:now+ms});
  return {setTimeout(fn,ms){timers.set(++next,{fn,at:now+ms});return next;},clearTimeout(id){timers.delete(id);},
    setInterval(fn,ms){every(++next,fn,ms);return next;},clearInterval(id){timers.delete(id);},
    advance(ms){now+=ms;for(const [id,t] of [...timers])if(t.at<=now){timers.delete(id);t.fn();}}};
}
const settle=async()=>{for(let i=0;i<10;i++)await new Promise(resolve=>setImmediate(resolve));};
// The next body is requested only after the previous asset's SHA-256 digest, which
// runs on another thread: on a loaded machine that took over 12,000 turns. So wait
// for the request itself, bounded in time so a download that never asks still fails.
async function requested(bodies,ms=10000){
  for(const end=Date.now()+ms;!bodies.waiting.length&&Date.now()<end;)
    await new Promise(resolve=>setImmediate(resolve));
  assert.ok(bodies.waiting.length,`no download requested its body within ${ms} ms`);
  return bodies.waiting.shift();
}
function feeds(){
  const waiting=[];
  return {waiting,stream(asset,signal){
    let control;const body=new ReadableStream({start(c){control=c;}});
    signal.addEventListener("abort",()=>control.error(new Error("download aborted")));
    waiting.push({asset,control});return body;
  }};
}

test("a slow but steady download completes; a quiet minute aborts it",async()=>{
  const time=clock(),bodies=feeds(),w=worker({timers:time,stream:bodies.stream});
  const installing=w.install();installing.catch(()=>{});
  for(let i=0;i<w.assets.length;i++){
    const {asset,control}=await requested(bodies);
    const bytes=new TextEncoder().encode(asset.body),half=bytes.length>>1;
    // Each asset takes 100 s, but bytes never stop for a minute.
    control.enqueue(bytes.slice(0,half));await settle();time.advance(50000);
    control.enqueue(bytes.slice(half));await settle();time.advance(50000);
    control.close();
  }
  assert.equal((await installing).ready,true);
  const stalledTime=clock(),stalled=feeds(),v=worker({timers:stalledTime,stream:stalled.stream});
  let outcome=null;v.install().then(()=>{outcome="installed";},error=>{outcome=error.message;});
  (await requested(stalled)).control.enqueue(new Uint8Array(1));await settle();
  // One millisecond short of a quiet minute the download still runs; at the minute it aborts.
  stalledTime.advance(59999);await settle();
  assert.equal(outcome,null);assert.equal(stalled.waiting.length,0);
  stalledTime.advance(1);await settle();
  assert.match(String(outcome),/aborted/);
  assert.equal((await v.ctx.offlineStatus()).ready,false);
  assert.ok(!v.caches.map.get(v.run("CACHE")).has(new URL("index.html",scope).href));
});

test("an installation abandoned for an hour is reclaimed by the next activation",async()=>{
  const caches=cacheStorage();let clock=1000;const now=()=>clock;
  const partial=worker({build:"ddd",caches,now,bad:"network"});
  await assert.rejects(partial.install(),/offline/);
  assert.ok(caches.map.has(partial.run("CACHE")));
  const a=worker({build:"aaa",caches,now});await a.install();
  clock+=3600000;await a.activate();
  assert.ok(caches.map.has(partial.run("CACHE")));  // an hour without progress: may still run
  clock+=1;await a.activate();
  assert.ok(!caches.map.has(partial.run("CACHE")));
  assert.equal((await a.ctx.offlineStatus()).ready,true);
});

test("a long installation request tells the page it is still working",async()=>{
  const time=clock(),bodies=feeds(),w=worker({timers:time,stream:bodies.stream});
  const replies=[];let done;
  w.handlers.message({data:{type:"INSTALL"},ports:[{postMessage:r=>replies.push(clean(r))}],waitUntil:p=>{done=p;}});
  for(let i=0;i<w.assets.length;i++){
    const {asset,control}=await requested(bodies);
    control.enqueue(new TextEncoder().encode(asset.body));await settle();
    time.advance(20000);control.close();
  }
  await done;
  assert.equal(replies.filter(r=>r.working).length,w.assets.length);
  assert.deepEqual(replies.at(-1),{build:"aaa",ready:true,assets:3});
  time.advance(60000);assert.equal(replies.length,w.assets.length+1);  // no heartbeat after the answer
});

function liveTab(id, build, url=scope) {
  return {id, url, postMessage(message, ports) {
    assert.equal(message.type, "DUPLOTRAIN_CLIENT_BUILD");
    ports[0].postMessage({type: message.type, build});
  }};
}
async function threeVersions(options={}) {
  const caches=cacheStorage(); let time=1000;
  const versions=[];
  for (const build of ["aaa", "bbb", "ccc"]) {
    const w=worker({build,caches,now:()=>time++,...options});
    await w.install();versions.push(w);
  }
  return versions;
}

test("a live A tab survives activation of B and C, then unpins when closed",async()=>{
  const live=[],clients=async()=>live;
  const caches=cacheStorage();let time=1000;
  const options={caches,clients,now:()=>time++};
  const a=worker({...options,build:"aaa"});await a.install();await a.activate();
  live.push(liveTab("old-tab","aaa"));
  const b=worker({...options,build:"bbb"});await b.install();await b.activate();
  const c=worker({...options,build:"ccc"});await c.install();await c.activate();
  assert.equal((await a.ctx.offlineStatus()).ready,true);
  assert.equal((await b.ctx.offlineStatus()).ready,true);
  c.setOffline(true);
  assert.match(await (await c.request("worker.js?v=aaa")).text(),/aaa/);
  // A newly created worker global has no saved in-memory client information.
  const fresh=worker({build:"ccc",caches:c.caches,clients});await fresh.activate();
  assert.equal((await a.ctx.offlineStatus()).ready,true);
  live.length=0;
  const d=worker({build:"ddd",caches:c.caches,clients});await d.install();await d.activate();
  assert.equal((await a.ctx.offlineStatus()).ready,false);
  assert.equal((await b.ctx.offlineStatus()).ready,false);
  assert.equal((await c.ctx.offlineStatus()).ready,true);
});

test("a legacy or suspended live tab pins all old caches without blocking activation",async()=>{
  const time=clock(),silent={id:"legacy",url:scope,postMessage(){}};
  const [a,b,c]=await threeVersions({timers:time,clients:async()=>[silent]});
  const activation=c.activate();await settle();time.advance(1500);await activation;
  assert.equal((await a.ctx.offlineStatus()).ready,true);
  assert.equal((await b.ctx.offlineStatus()).ready,true);
});

test("a tab which closes during the handshake no longer pins caches",async()=>{
  const time=clock();let checks=0;
  const silent={id:"closing",url:scope,postMessage(){}};
  const [a,,c]=await threeVersions({timers:time,clients:async()=>++checks===1?[silent]:[]});
  const activation=c.activate();await settle();time.advance(1500);await activation;
  assert.equal((await a.ctx.offlineStatus()).ready,false);
});

test("new clients during enumeration conservatively stop pruning",async()=>{
  let checks=0;
  const [a,b,c]=await threeVersions({clients:async()=>++checks===1?[]:[liveTab("new","aaa")]});
  await c.activate();
  assert.equal((await a.ctx.offlineStatus()).ready,true);
  assert.equal((await b.ctx.offlineStatus()).ready,true);
});

test("failed client enumeration and unknown build identities retain backups",async()=>{
  for (const clients of [async()=>{throw new Error("client enumeration failed");},
    async()=>[liveTab("unknown","fff")]]) {
    const [a,b,c]=await threeVersions({clients});await c.activate();
    assert.equal((await a.ctx.offlineStatus()).ready,true);
    assert.equal((await b.ctx.offlineStatus()).ready,true);
  }
});

test("clients outside this scope do not pin this application's caches",async()=>{
  const [a,,c]=await threeVersions({clients:async()=>[
    {id:"other",url:"https://example.test/another/",postMessage(){throw new Error("not our client");}}
  ]});
  await c.activate();assert.equal((await a.ctx.offlineStatus()).ready,false);
});

test("all content versions sharing a live tab's build stamp are retained",async()=>{
  const caches=cacheStorage(),clients=async()=>[liveTab("same-build","aaa")];let time=1000;
  const options={caches,clients,now:()=>time++};
  const a=worker({...options,build:"aaa"});await a.install();await a.activate();
  const a2=worker({...options,build:"aaa",page:" second content version"});await a2.install();
  const b=worker({...options,build:"bbb"});await b.install();await b.activate();
  const c=worker({...options,build:"ccc"});await c.install();await c.activate();
  assert.notEqual(a.run("CACHE"),a2.run("CACHE"));
  assert.equal((await a.ctx.offlineStatus()).ready,true);
  assert.equal((await a2.ctx.offlineStatus()).ready,true);
});

test("boot answers with its immutable document build without starting or installing anything",()=>{
  let listener;
  const context=vm.createContext({window:{},navigator:{serviceWorker:{
    addEventListener(type,callback){assert.equal(type,"message");listener=callback;}
  }}});
  const source=fs.readFileSync(path.join(__dirname,"../../webapp/boot.js"),"utf8");
  vm.runInContext(source.replaceAll("__BUILD__","abc12345"),context);
  context.window.duplotrainBuild="newer-controller";
  const replies=[],port={postMessage:reply=>replies.push(clean(reply))};
  listener({data:{type:"DUPLOTRAIN_CLIENT_BUILD"},ports:[port]});
  assert.deepEqual(replies,[{type:"DUPLOTRAIN_CLIENT_BUILD",build:"abc12345"}]);
  listener({data:{type:"OTHER"},ports:[port]});
  listener({data:{type:"DUPLOTRAIN_CLIENT_BUILD"},ports:[]});
  assert.equal(replies.length,1);
});
