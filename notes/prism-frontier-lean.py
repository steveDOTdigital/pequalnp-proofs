"""Emit the Lean data for the signed triangular-prism certificate."""
from pathlib import Path
import argparse
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
MASK = (1 << 64) - 1


def mix(w):
    z = (w ^ (w >> 30)) * 0xbf58476d1ce4e5b9 & MASK
    z = (z ^ (z >> 27)) * 0x94d049bb133111eb & MASK
    return z ^ (z >> 31)


def read_layers():
    with tempfile.TemporaryDirectory(prefix="pnp-prism-data-") as tmp:
        binary = Path(tmp) / "frontier"
        subprocess.run(["c++", "-O3", "-std=c++17", str(HERE / "prism-frontier-certificate.cpp"), "-o", str(binary)], check=True)
        data = subprocess.check_output([str(binary), "--dump"], text=True)
    assert not Path(tmp).exists()
    states = [[] for _ in range(10)]
    images = [[] for _ in range(10)]
    actions = []
    for line in data.splitlines():
        tag, *fields = line.split()
        values = list(map(int, fields))
        if tag == "S":
            k, i, *state = values
            assert i == len(states[k])
            states[k].append(state)
        elif tag == "L":
            k, i, action, *state = values
            images[k].append((state, i, action))
        else:
            i, *perm = values
            assert tag == "P" and i == len(actions)
            actions.append(perm)
    return states, images, actions


def packed(x, width):
    n = 0
    for v in reversed(x):
        assert 0 <= v < 1 << width
        n = (n << width) | v
    return n


def paged(name, layers, widths):
    lines = [f"def {name} (k page : ℕ) : ℕ :=", "  match k, page with"]
    for k, values in enumerate(layers):
        for i in range(0, len(values), 64):
            block = packed(values[i:i+64], widths[k])
            lines.append(f"  | {k}, {i//64} => 0x{block:x}")
    return "\n".join(lines + ["  | _, _ => 0", ""])


def function(name, values):
    lines = [f"def {name} : ℕ → ℕ"]
    lines.extend(f"  | {i} => {v}" for i, v in enumerate(values) if v)
    return "\n".join(lines + ["  | _ => 0", ""])


def generate():
    states, images, actions = read_layers()
    terms = ["import PrismFrontierData", "", "namespace PrismSignedFrontier.Certificate", "open Prism", ""]
    dictionary = sorted({w for group in states for pool in group for w in pool})
    width = len(dictionary).bit_length()
    word_id = {w: i+1 for i,w in enumerate(dictionary)}
    digits = [[packed([word_id[w] for w in pool], width) for pool in group] for group in states]
    terms += [paged("dictionary", [[0]+dictionary], [64]),
              paged("encodedPool", digits, [width*(k+1) for k in range(10)]),
              function("counts", list(map(len,states)))]
    terms += [f"""def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % {1 << width}
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> {width})

def pool (k i : ℕ) := decode (k+1) (field encodedPool k ({width}*(k+1)) i)
"""]
    salt = 0
    while True:
        keyed = [sorted(((sum(mix(w+salt & MASK) for w in s) & 0xffffffff, i*16+a)
                         for s,i,a in group)) for group in images]
        if all(len(set(key for key,_ in group)) == len(group) for group in keyed): break
        salt += 1
    terms += [function("entries",list(map(len,keyed))),
              paged("keys", [[x for x,_ in group] for group in keyed], [32]*10),
              paged("targets", [[v for _,v in group] for group in keyed], [16]*10)]
    terms += [f"""def mix (w : W) : W :=
  let u := w + {salt}
  let v := (u ^^^ (u >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (v ^^^ (v >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def key (xs : List W) := (xs.foldl (fun h x => h + mix x) (0 : W)).toNat % 4294967296

def search (k h : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel+1, lo, hi =>
    if lo+1 < hi then
      let m := (lo+hi)/2
      if field keys k 32 m ≤ h then search k h fuel m hi else search k h fuel lo m
    else lo

def lookup (k : ℕ) (xs : List W) : ℕ × ℕ :=
  let ix := search k (key xs) 14 0 (entries k)
  let slot := field targets k 16 ix
  (slot / 16,slot % 16)
"""]
    swaps = {}
    sequences = []
    for perm in actions:
        now = list(range(6))
        sequence = []
        for i, p in enumerate(perm):
            if now[i] == p: continue
            a,b = sorted((now[i],p))
            now = [b if v==a else a if v==b else v for v in now]
            name = f"s{a}{b}"
            if name not in swaps:
                low = sum(1 << r for r in range(64) if r>>a&1 and not r>>b&1)
                high = sum(1 << r for r in range(64) if r>>b&1 and not r>>a&1)
                swaps[name] = (2**b-2**a,low,high)
            sequence.append(name)
        assert now == perm
        sequences.append(sequence)
    for name,(d,lo,hi) in swaps.items():
        terms += [f"def {name} : Switch := ⟨{d},0x{lo:x},0x{hi:x}⟩",
                  f"theorem {name}_ok : {name}.Valid := by unfold Switch.Valid; decide +kernel"]
    terms += ["", "def steps : ℕ → List Switch"]
    terms += [f"  | {i} => [{', '.join(s)}]" for i,s in enumerate(sequences) if s]
    terms += ["  | _ => []","", "theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by",
              "  unfold steps","  split <;> simp [" +
              ", ".join(name+"_ok" for name in swaps)+"]", "",
              "theorem fix (j : ℕ) : reindex (steps j) target = target := by",
              "  unfold steps","  split <;> decide +kernel","",
              "def checked (k i : ℕ) := decide (pool k i).Nodup && closed target negative pool counts lookup steps k i",
              "", "theorem root : pool 9 0 = raw := by decide +kernel\n\ntheorem lower_from_checks\n    (verified : ∀ k ≤ 9, ∀ i < counts k, checked k i = true)\n    (p : List (ℕ × ℕ)) (o : ℕ) (hit : canonical (evaluate p initial o) = target) :\n    10 ≤ p.length := by\n  by_contra! short\n  have access : {target} ⊆ available (p.foldl add initial) := by\n    apply Finset.singleton_subset_iff.mpr\n    rw [← hit]\n    exact available_read _ _\n  obtain ⟨k,s,bound,inside,run⟩ := extract p initial target 0 {target} Cone.done access\n  rw [start] at inside\n  have eq := run.initial nonzero raw essential inside\n  rw [eq,← root] at run\n  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 9\n    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)\n    (fun k hk i hi => (Bool.and_eq_true_iff.mp (verified k hk i hi)).2) 9 le_rfl 0\n    (by decide +kernel) k (by omega) run\n\n", "end PrismSignedFrontier.Certificate", ""]
    return "\n".join(terms)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("out",type=Path)
    path = parser.parse_args().out
    with path.open("x") as out:
        out.write(generate())
