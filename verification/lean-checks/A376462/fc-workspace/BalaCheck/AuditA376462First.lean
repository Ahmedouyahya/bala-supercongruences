import BalaCheck.A376462First
#print axioms A376462_first
#print axioms A376462Proof.cong
#print axioms A376462Proof.T_scaled_int
#print axioms A376462Proof.SK_dvd
#print axioms A376462Proof.SI_dvd
#print axioms A376462Proof.rep
/-- the first conjunct of the target, read from the target type -/
example : type_of% @oeis_376462_conjecture_0 → type_of% @A376462_first :=
  fun h p n r hp hp5 hn hr => (h p n r hp hp5 hn hr).1
