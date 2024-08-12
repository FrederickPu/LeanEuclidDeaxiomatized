Getting LeanEuclid to support structures consists of the following steps:
- Change SystemE/Theory
- Change SystemE/Meta/smt/translator
- Show that every instance of EuclideanSpace (from Mathlib4) is also an instance of the structure defined in SystemE/Theory
