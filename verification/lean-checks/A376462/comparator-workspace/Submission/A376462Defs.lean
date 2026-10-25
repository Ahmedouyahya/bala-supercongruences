/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports
open Nat Finset

/--
A helper function for the $A108625$ array:
$$A108625(n, k) = \sum_{i=0}^k \binom{n}{i}^2 \binom{n+k-i}{k-i}$$
-/
noncomputable def a108625_aux (n k : ℕ) : ℕ :=
  (range (k + 1)).sum fun i =>
    (n.choose i) ^ 2 * ((n + k - i).choose (k - i))

/--
A376462: $a(n) = \sum_{k = 0..n} \binom{n}{k}^2 \binom{n+k}{k} A108625(n, n-k)$.
-/
noncomputable def A376462 (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k =>
    (n.choose k) ^ 2 * (n + k).choose k * (a108625_aux n (n - k))
