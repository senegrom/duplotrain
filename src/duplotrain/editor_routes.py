"""Cooperative route optimisation over the existing train model, never a new model."""
from __future__ import annotations

import math
import time
import uuid
from collections import Counter

from .drive import (
    DriveLimitError,
    _all_starts,
    _cycle_both_directions,
    _tongue_assignments,
    _tongue_choices,
    drivable_universe,
    drive,
)
from .editor_search import MAX_JOB_SECONDS, integer


class RouteJob:
    def __init__(self, session, body):
        from .editor import _end

        self.id, self.revision = uuid.uuid4().hex, session.revision
        self.layout = session.layout
        if not self.layout or self.layout.joint_issues():
            raise ValueError("Train analysis needs track with compatible joints")
        self.starts = _all_starts(self.layout)
        scope = body.get("scope", "all")
        if scope not in ("all", "selected"):
            raise ValueError("route scope must be all or selected")
        if scope == "selected":
            start = _end(body.get("start"), "start")
            if start not in self.starts:
                raise ValueError("choose an inward port of drivable track")
            self.starts = [start]
        self.scope = scope
        self.goal = body.get("goal", "visited")
        if self.goal not in ("visited", "cycle"):
            raise ValueError("route goal must be visited or cycle")
        self.max_runs = integer(body.get("max_runs", 20000), 1, 100000, "max_runs")
        self.max_steps = integer(body.get("max_steps", 10000), 1, 10000, "max_steps")
        self.required = len(self.starts) * math.prod(
            len(o) for _, o in _tongue_choices(self.layout))
        if not self.required:
            raise ValueError("No drivable starting positions")
        self.universe = drivable_universe(self.layout)
        self.iterator = ((start, settings) for settings in _tongue_assignments(self.layout)
                         for start in self.starts)
        self.runs = self.steps = self.limited_runs = 0
        self.outcomes = Counter()
        self.best = self.best_score = None
        # The first run breaking each universal property, as drive.classify
        # records them: the counterexample breaks the weakest one that failed.
        self.failures = {}
        self.locally = False
        self.looping = self.completely = self.perfectly = True
        self.status = "running"
        self.complete = False
        self.last_touch = time.monotonic()

    def tick(self):
        if self.status != "running":
            return
        deadline = time.perf_counter() + 0.02
        for _ in range(32):
            if self.runs >= min(self.required, self.max_runs) or self.steps >= 10_000_000:
                self.complete = self.runs == self.required and not self.limited_runs
                self.status = "complete" if self.complete else "limited"
                return
            start, settings = next(self.iterator)
            self.runs += 1
            try:
                report = drive(self.layout, start=start, switch_states=settings,
                               max_steps=self.max_steps)
            except DriveLimitError:
                self.limited_runs += 1
                self.steps += self.max_steps
                if time.perf_counter() >= deadline:
                    return
                continue
            self.steps += len(report.steps)
            self.outcomes[report.outcome] += 1
            visited = len(report.visited & self.universe)
            cycle = (len({step[0] for step in report.steps[report.cycle_start:]} & self.universe)
                     if report.cycle_start is not None else 0)
            score = ((cycle, visited) if self.goal == "cycle" else (visited, cycle))
            score += (report.outcome == "endless", -len(report.steps))
            witness = {"start": list(start), "switch_states": dict(settings),
                       "visited": visited, "cycle_visited": cycle, "outcome": report.outcome,
                       "period": report.period}
            if self.best is None or score > self.best_score:
                self.best, self.best_score = witness, score
            if report.outcome == "endless":
                self.locally = True
                if not report.visited >= self.universe:
                    self.completely = self.perfectly = False
                    self.failures.setdefault("completely", witness)
                elif self.perfectly and not _cycle_both_directions(report, self.layout):
                    self.perfectly = False
                    self.failures.setdefault("perfectly", witness)
            else:
                self.looping = self.completely = self.perfectly = False
                self.failures.setdefault("looping", witness)
            if time.perf_counter() >= deadline:
                break

    def response(self):
        # Universal booleans appear only after EVERY requested run returned a verdict.
        classification = None
        if self.complete:
            classification = {"locally_looping": self.locally,
                              "looping": self.locally and self.looping,
                              "completely_looping": self.locally and self.completely,
                              "perfectly_looping": self.locally and self.perfectly}
        counterexample_property = next((key for key in ("looping", "completely", "perfectly")
                                        if key in self.failures), None)
        return {"job_id": self.id, "revision": self.revision, "status": self.status,
                "scope": self.scope, "goal": self.goal, "runs": self.runs,
                "required_runs": str(self.required), "max_runs": self.max_runs,
                "max_steps": self.max_steps, "step_limited_runs": self.limited_runs,
                "steps": self.steps, "total_drivable": len(self.universe),
                "best": self.best, "counterexample": self.failures.get(counterexample_property),
                "counterexample_property": counterexample_property,
                "outcomes": dict(self.outcomes), "classification": classification,
                "complete": self.complete, "optimal": self.complete,
                "model_only": True}

    def close(self):
        iterator, self.iterator = self.iterator, None
        if iterator is not None:
            iterator.close()
        self.status = "discarded"


def dispatch_routes(session, path, body):
    action = path.removeprefix("/api/routes/")
    if action == "start":
        job = RouteJob(session, body)
        old = session._interactive_job
        if old is not None:
            old.close()
        session._interactive_job = job
    else:
        job = session._interactive_job
        if (not isinstance(job, RouteJob) or body.get("job_id") != job.id
                or session.revision != job.revision):
            raise ValueError("This train analysis is no longer active")
        if time.monotonic() - job.last_touch > MAX_JOB_SECONDS:
            job.close()
            session._interactive_job = None
            raise ValueError("Train analysis expired; start again")
        if action == "tick":
            try:
                job.tick()
            except Exception:
                job.close()
                session._interactive_job = None
                raise
        elif action == "pause":
            if job.status == "running":
                job.status = "paused"
        elif action == "resume":
            if job.status == "paused":
                job.status = "running"
        elif action == "discard":
            job.close()
            session._interactive_job = None
        else:
            raise ValueError("unknown train analysis action")
    job.last_touch = time.monotonic()
    return job.response()
