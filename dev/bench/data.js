window.BENCHMARK_DATA = {
  "lastUpdate": 1784739145493,
  "repoUrl": "https://github.com/naveen-seth/veir",
  "entries": {
    "VeIR Benchmarks": [
      {
        "commit": {
          "author": {
            "email": "naveen.hanig@outlook.com",
            "name": "Naveen Seth Hanig",
            "username": "naveen-seth"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "939aa512d6ca9c65fe203a282c4ca8137bacd2a4",
          "message": "feat(rewriter): Add setAttributes, setProperties with GetSet lemmas (#1108)\n\nThis adds `setAttributes` and `setProperties` to `Rewriter/WfRewriter`,\nwith corresponding GetSet lemmas for each.\nThis also adds the same proof about `WellFormed` for `setProperties`\nthat already exists for `setAttributes`.\n\nThe initial motivation for this was to remove the current `sorry`s in\n`setFunctionType` (`Passes/CastsReconciliation/Reconciliation.lean`).\nThis and other potential call sites will be updated in follow-ups to\nkeep this smaller.\n\n---------\n\nCo-authored-by: Mathieu Fehr <mathieu.fehr@gmail.com>",
          "timestamp": "2026-07-22T01:25:14Z",
          "tree_id": "ad734bc4bb2012797a852014f29099c1e7400cef",
          "url": "https://github.com/naveen-seth/veir/commit/939aa512d6ca9c65fe203a282c4ca8137bacd2a4"
        },
        "date": 1784739144863,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2253000,
            "range": "± 83656",
            "unit": "ns",
            "extra": "count=1000 pc=100 samples=5 median=0.002253s stddev=0.000083656s cv=3.7353%"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3940000,
            "range": "± 45714",
            "unit": "ns",
            "extra": "count=1000 pc=100 samples=5 median=0.003940s stddev=0.000045714s cv=1.1613%"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2236000,
            "range": "± 112908",
            "unit": "ns",
            "extra": "count=1000 pc=100 samples=11 median=0.002236s stddev=0.000112908s cv=4.9691%"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3696000,
            "range": "± 42571",
            "unit": "ns",
            "extra": "count=1000 pc=100 samples=11 median=0.003696s stddev=0.000042571s cv=1.1471%"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2285000,
            "range": "± 114786",
            "unit": "ns",
            "extra": "count=1000 pc=100 samples=12 median=0.002285000s stddev=0.000114786s cv=4.9573%"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2602000,
            "range": "± 52603",
            "unit": "ns",
            "extra": "count=1000 pc=100 samples=12 median=0.002602000s stddev=0.000052603s cv=2.0269%"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1832000,
            "range": "± 89790",
            "unit": "ns",
            "extra": "count=1000 pc=100 samples=11 median=0.001832s stddev=0.000089790s cv=4.8542%"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 2168000,
            "range": "± 55367",
            "unit": "ns",
            "extra": "count=1000 pc=100 samples=11 median=0.002168s stddev=0.000055367s cv=2.5486%"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2262000,
            "range": "± 34405",
            "unit": "ns",
            "extra": "count=1000 pc=100 samples=5 median=0.002262s stddev=0.000034405s cv=1.5283%"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5485000,
            "range": "± 44140",
            "unit": "ns",
            "extra": "count=1000 pc=100 samples=5 median=0.005485s stddev=0.000044140s cv=0.8039%"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2247000,
            "range": "± 102921",
            "unit": "ns",
            "extra": "count=1000 pc=100 samples=7 median=0.002247s stddev=0.000102921s cv=4.6525%"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2988000,
            "range": "± 25459",
            "unit": "ns",
            "extra": "count=1000 pc=100 samples=7 median=0.002988s stddev=0.000025459s cv=0.8511%"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2250000,
            "range": "± 79276",
            "unit": "ns",
            "extra": "count=1000 pc=100 samples=5 median=0.002250s stddev=0.000079276s cv=3.5284%"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1932000,
            "range": "± 13465",
            "unit": "ns",
            "extra": "count=1000 pc=100 samples=5 median=0.001932s stddev=0.000013465s cv=0.6946%"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1874000,
            "range": "± 59235",
            "unit": "ns",
            "extra": "count=1000 pc=100 samples=5 median=0.001874s stddev=0.000059235s cv=3.1926%"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1543000,
            "range": "± 41717",
            "unit": "ns",
            "extra": "count=1000 pc=100 samples=5 median=0.001543s stddev=0.000041717s cv=2.6731%"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2163000,
            "range": "± 80993",
            "unit": "ns",
            "extra": "count=1000 pc=100 samples=5 median=0.002163s stddev=0.000080993s cv=3.7180%"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3665000,
            "range": "± 55136",
            "unit": "ns",
            "extra": "count=1000 pc=100 samples=5 median=0.003665s stddev=0.000055136s cv=1.5106%"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1855500,
            "range": "± 73493",
            "unit": "ns",
            "extra": "count=1000 pc=100 samples=30 median=0.001855500s stddev=0.000073493s cv=3.9565%"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "range": "± 2804",
            "unit": "ns",
            "extra": "count=1000 pc=100 samples=30 median=0.000008000s stddev=0.000002804s cv=31.1556%"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1950000,
            "range": "± 92704",
            "unit": "ns",
            "extra": "count=1000 pc=100 samples=11 median=0.001950s stddev=0.000092704s cv=4.7837%"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 782000,
            "range": "± 20949",
            "unit": "ns",
            "extra": "count=1000 pc=100 samples=11 median=0.000782s stddev=0.000020949s cv=2.6539%"
          }
        ]
      }
    ]
  }
}