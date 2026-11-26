"""Recheck the recorded Petersen exclusions, proving each premise before use.

Searches operate independently across reader profiles. Within a profile, a
strengthened case runs only after this replay has excluded all its prerequisites.
"""
import argparse
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import runpy
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
NOTE = HERE / "petersen-internal-not-4727.md"
SEARCH = runpy.run_path(str(HERE / "petersen-internal-not-4727.py"))
TOTAL = 1581
START = "<!-- petersen-replay:start -->\n```json\n"
END = "\n```\n<!-- petersen-replay:end -->"


def load_checkpoint():
    note = NOTE.read_text(encoding="utf-8")
    if note.count(START) != 1 or note.count(END) != 1:
        raise ValueError("Expected a single replay checkpoint in the research note.")
    return json.loads(note.split(START, 1)[1].split(END, 1)[0])


def plans(cases, ledger):
    tags = list(cases)
    prefix = ledger["first_pass_prefix"]
    if len(tags) != TOTAL or not 0 <= prefix <= TOTAL:
        raise ValueError("Unexpected enumeration size or checkpoint boundary.")
    baseline = set(tags[:prefix])
    profiles = defaultdict(list)
    for mask, seed in tags:
        profiles[mask].append(seed)
    exceptions = ledger["exceptions"]
    if not set(exceptions) <= {str(mask) for mask in profiles}:
        raise ValueError("Unknown reader profile in checkpoint.")
    result = {}
    ordinary = 0
    for mask, seeds in profiles.items():
        unknown, retries = exceptions.get(str(mask), ["0x0", []])
        unknown = int(unknown, 16)
        if unknown < 0 or unknown >> len(seeds):
            raise ValueError(f"Unknown gate index in profile {mask}.")
        jobs = []
        done = 0
        for idx, seed in enumerate(seeds):
            bit = 1 << idx
            if (mask, seed) in baseline and not (unknown & bit):
                jobs.append((seed, ()))
                done |= bit
                ordinary += 1
        for idx, encoded in retries:
            if not 0 <= idx < len(seeds):
                raise ValueError(f"Invalid retry index in profile {mask}.")
            bit = 1 << idx
            prem = int(encoded, 16)
            if not (unknown & bit) or done & bit or prem < 0 or prem & ~done:
                raise ValueError(f"Invalid or unproved prerequisite in profile {mask}, seed {idx}.")
            required = tuple(s for j, s in enumerate(seeds) if prem & (1 << j))
            jobs.append((seeds[idx], required))
            done |= bit
        result[mask] = jobs
    if ordinary != ledger["first_pass_unsat"] or sum(map(len, result.values())) != ledger["confirmed"]:
        raise ValueError("The planned cases disagree with the recorded totals.")
    return result


def run_case(exe, data, seconds):
    output = subprocess.check_output([str(exe)], input=data, text=True, timeout=seconds + 60)
    return output.strip().splitlines()


def recheck_profile(mask, jobs, cases, exe, seconds):
    verified = set()
    for seed, required in jobs:
        tag = mask, seed
        if not set(required) <= verified:
            raise ValueError(f"Prerequisite has not passed this replay: {tag}")
        data = SEARCH["omit_verified_raw_orbits"](cases[tag], tag, [(mask, s) for s in required])
        lines = run_case(exe, data, seconds)
        if len(lines) != 1 or not lines[0].startswith("UNSAT ") or not lines[0][6:].isdigit():
            raise RuntimeError(f"Case {tag} did not pass: {lines}")
        verified.add(seed)
    return len(verified)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-plan", action="store_true", help="validate dependencies and counts without running the solver")
    parser.add_argument("--profile", type=int, help="replay only this reader profile")
    parser.add_argument("--seconds", type=int, default=2700, help="time limit per case")
    parser.add_argument("--workers", type=int, default=2, help="number of profiles rechecked in parallel")
    args = parser.parse_args()
    if min(args.seconds, args.workers) <= 0:
        parser.error("Time limit and worker count must be positive.")
    driver = SEARCH["driver"]
    floors, lower = driver["bounds"](10, False)
    cases = {tag: data for tag, data in driver["problems"](10, False, 18, args.seconds, floors, lower)
             if tag[1][0] in (0, 3)}
    work = plans(cases, load_checkpoint())
    if args.profile is not None:
        if args.profile not in work:
            parser.error("Unknown reader profile.")
        work = {args.profile: work[args.profile]}
    count = sum(map(len, work.values()))
    print(f"Replay plan: {count} of {TOTAL} cases.", flush=True)
    if args.check_plan:
        return
    if not count:
        parser.error("No completed exclusions in the selected part of this checkpoint.")
    SEARCH["verify_slices"]()
    with tempfile.TemporaryDirectory(prefix="petersen-4727-replay-") as directory:
        exe = SEARCH["build"](Path(directory))
        control = run_case(exe, driver["control"](10, args.seconds, floors, lower), args.seconds)
        if not control or not control[-1].startswith("SAT "):
            raise RuntimeError("The known 20-gate circuit failed its positive control.")
        def check(item):
            mask, jobs = item
            return recheck_profile(mask, jobs, cases, exe, args.seconds)
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            completed = sum(pool.map(check, work.items()))
    if Path(directory).exists() or completed != count:
        raise RuntimeError("Replay did not finish cleanly.")
    print(f"Rechecked {completed} of {TOTAL} cases with the external solver.", flush=True)


if __name__ == "__main__":
    main()
