"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness, scene} = require("./reliability-harness.cjs");
function setup() {
  const h=harness({state:scene(),overrides:{redraw(){},renderCandidates(){},renderJobControls(){},driveRouteTicks:async()=>{}}});
  h.run(`S.instance="engine";jobSequence=1;
    interactiveJob={job_id:"search",revision:1,page:0,found:16,candidates:[]};
    window.published={...S,revision:2,candidates:[],search_job:{job_id:"search",revision:2,page:0,found:16,
      candidates:[{index:0,revision:2,preview:{base_revision:2}}]}};
    api=async()=>window.published;`);
  return h;
}
for(const page of [0,1]) test(`published page ${page+1} remains available after route analysis`,async()=>{
  const h=setup();
  await h.run('publishSearch(1)');
  assert.equal(h.run('S.candidates===interactiveJob.candidates'),true);
  if(page){
    h.run('api=async()=>({...interactiveJob,page:1,candidates:[{index:8,revision:2,preview:{base_revision:2}}]})');
    await h.run('searchPageTo(1)');
  }
  assert.equal(h.run('S.candidates===interactiveJob.candidates'),true);
  h.run('window.retained=S.candidates;api=async()=>({job_id:"route",revision:2,status:"complete"})');
  await h.run('startRouteAnalysis("all")');
  assert.equal(h.run('interactiveJob'),null);
  assert.equal(h.run('visibleCandidates()===window.retained'),true);
  assert.equal(h.run('visibleCandidates()[0].index'),page?8:0);
});
for(const change of ['interactiveJob.revision=99','S.search_job.job_id="other"','S.search_job.revision=99','delete S.search_job']) {
  test(`unpublished/stale page cannot replace fallback: ${change}`,async()=>{
    const h=setup();await h.run('publishSearch(1)');
    h.run(`window.retained=S.candidates;interactiveJob={...interactiveJob,candidates:[{index:9}]};${change};retainPublishedPage()`);
    assert.equal(h.run('S.candidates===window.retained'),true);
  });
}
