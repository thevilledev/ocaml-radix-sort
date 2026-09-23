#!/usr/bin/env python3
"""Print a TLC counterexample of ParallelRadixSort.tla one state per line.

    python3 trace_summary.py results/ParallelRadixSort_original_spawnfail.out

Works with and without TLC's -difftrace.  Elements <<key, id>> are shown as
key#id, and the tmp filler <<0, -1>> as "_".
"""
import re
import sys


def elems(value):
    items = re.findall(r"\d+ :> <<(-?\d+), (-?\d+)>>", value)
    return " ".join("_" if i == "-1" else f"{k}#{i}" for k, i in items)


def seq(value):
    return ",".join(x.strip().strip('"') for x in value.strip("<> ").split(",") if x.strip())


def main(path):
    text = open(path).read()
    err = re.search(r"Error: (.*violated.*)", text)
    if "State 1:" not in text:
        print("no counterexample in", path)
        return
    print(err.group(1) if err else "")
    states = re.split(r"\n(?=State \d+: )", text[text.index("State 1:"):])
    cur = {}
    header = (f"{'#':>3} {'action':12} {'sort':8} {'main':9} {'shift':>5} "
              f"{'phase':8} {'src':4} {'caller':12} {'domains (state/i)':30} "
              f"{'a':16} tmp")
    print(header)
    print("-" * len(header))
    for st in states:
        head = st.split("\n", 1)[0]
        m = re.match(r"State (\d+): <(\w+)", head)
        if not m:
            continue
        for line in st.split("\n")[1:]:
            mm = re.match(r"/\\ (\w+) = (.*)", line)
            if mm:
                cur[mm.group(1)] = mm.group(2)
        action = "Init" if m.group(2) == "Initial" else m.group(2)
        caller = (f"f{cur['cw']}:{cur['cstage'].strip(chr(34))}@{cur['ci']}"
                  if cur["mpc"] == '"f"' else "-")
        states_ = seq(cur["dstate"]).split(",") if seq(cur["dstate"]) else []
        idx = seq(cur["di"]).split(",") if seq(cur["di"]) else []
        doms = " ".join(f"d{n + 1}={s}/{i}" for n, (s, i) in enumerate(zip(states_, idx)))
        src = "a" if cur["fromA"] == "TRUE" else "tmp"
        print(f"{m.group(1):>3} {action:12} {cur['ret'].strip(chr(34)):8} "
              f"{cur['mpc'].strip(chr(34)):9} {cur['shift']:>5} "
              f"{cur['phase'].strip(chr(34)):8} {src:4} {caller:12} {doms or '-':30} "
              f"{elems(cur['a']):16} {elems(cur['tmp'])}")


if __name__ == "__main__":
    for p in sys.argv[1:]:
        main(p)
