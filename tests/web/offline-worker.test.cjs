"use strict";
const {test}=require("node:test"), assert=require("node:assert/strict");
const fs=require("node:fs"), path=require("node:path"), vm=require("node:vm");
const {createHash,webcrypto}=require("node:crypto");
const template=fs.readFileSync(path.join(__dirname,"../../webapp/service-worker.js"),"utf8");
const scope="https://example.test/duplotrain/";
const clean=x=>JSON.parse(JSON.stringify(x));
function cacheStorage(){
  const map=new Map();let failedPut=false;
  return {map,failPut(value=true){failedPut=value;},async keys(){return [...map.keys()];},
    async delete(key){return map.delete(key);},async open(key){
      if(!map.has(key))map.set(key,new Map());const store=map.get(key);
      const name=k=>typeof k==="string"?k:k.url;
      return {async match(k){return store.get(name(k))?.clone();},async put(k,v){
        if(failedPut)throw new Error("quota exceeded");store.set(name(k),v.clone());},
        async delete(k){return store.delete(name(k));}};
    }};
}
function worker({build="aaa",caches=cacheStorage(),bad=null,now=()=>Date.now()}={}){
  const assets=[{url:"index.html",body:`<html>build ${build}</html>`},
    {url:`editor.js?v=${build}`,body:`const build='${build}'`},
    {url:`worker.js?v=${build}`,body:`const engine='${build}'`}];
  const manifest=assets.map(a=>({url:a.url,bytes:Buffer.byteLength(a.body),
    sha256:createHash("sha256").update(a.body).digest("hex")}));
  const handlers={},calls=[];let offline=false,activated=0;
  const fetch=async req=>{
    const url=typeof req==="string"?req:req.url;calls.push(url);
    if(offline||bad==="network")throw new Error("offline");
    const asset=assets.find(a=>new URL(a.url,scope).href===url);
    const body=bad===asset?.url?"corrupt":asset?.body||"network fallback";
    return new Response(body,{headers:{"Content-Type":asset?.url==="index.html"?"text/html":"application/javascript",
      "Content-Security-Policy":"default-src 'self'","Content-Encoding":"gzip"}});
  };
  const ctx=vm.createContext({URL,Response,Request,Headers,Uint8Array,ArrayBuffer,AbortController,
    crypto:webcrypto,caches,fetch,setTimeout,clearTimeout,Date:{now},
    self:{registration:{scope},clients:{claim:async()=>{}},skipWaiting:async()=>{activated++;},
      addEventListener:(name,fn)=>{handlers[name]=fn;}}});
  vm.runInContext(template.replaceAll("__BUILD__",build).replace("__ASSETS__",JSON.stringify(manifest)),ctx);
  const run=code=>vm.runInContext(code,ctx);
  return {ctx,run,caches,assets,manifest,handlers,calls,setOffline:v=>{offline=v;},activated:()=>activated,
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

for(const bad of ["index.html","editor.js?v=bbb","network"])test(`failed version ${bad} preserves verified old version and unrelated caches`,async()=>{
  const caches=cacheStorage(),old=worker({caches});await old.install();
  const other=await caches.open("other-app");await other.put("https://example.test/other",new Response("do not delete"));
  const next=worker({build:"bbb",caches,bad});await assert.rejects(next.install(),/offline|verification/);
  assert.equal((await next.ctx.offlineStatus()).ready,false);
  assert.equal((await old.ctx.offlineStatus()).ready,true);
  assert.ok(caches.map.has("other-app"));assert.equal(next.activated(),0);
  assert.ok(!caches.map.has(next.run("CACHE")));
});

test("quota failure cannot mark a partial installation ready",async()=>{
  const w=worker();w.caches.failPut();await assert.rejects(w.install(),/quota/);
  assert.equal((await w.ctx.offlineStatus()).ready,false);
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
  const partial=worker({build:"ddd",caches,now});await (await caches.open(partial.run("CACHE"))).put(
    new URL("index.html",scope).href,new Response("still installing"));
  await versions[2].activate();
  const kept=[...caches.map.keys()];
  assert.ok(kept.includes("other-app")&&kept.includes(partial.run("CACHE")));
  assert.ok(kept.includes(versions[2].run("CACHE"))&&kept.includes(versions[1].run("CACHE")));
  assert.ok(!kept.includes(versions[0].run("CACHE")));
  // Tabs still running the previous version keep its exact assets offline.
  versions[2].setOffline(true);
  assert.match(await (await versions[2].request("editor.js?v=bbb")).text(),/bbb/);
});

