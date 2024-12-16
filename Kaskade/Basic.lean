
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open BigOperators

#check StrictMonoOn

#check Nat.choose

#eval Nat.choose 4 2

#check Finset.Icc

#eval Finset.Icc 2 5

#check StrictMonoOn

/-

lemma cascade (m : ℕ) :
  ∃ s, ∃ (hs : 1 ≤ s),  ∃ k, ∃ hk : s ≤ k,
  ∃ a : {x : ℕ // x ∈ Finset.Icc s k} → ℕ,
  a s ≥ s ∧
  StrictMonoOn ∧
  m = ∑ i in (Finset.univ : Finset {x : ℕ // x ∈ Finset.Icc s k}), Nat.choose (a i) i :=
  by
  sorry


-/


lemma cascade (m k: ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m):
  ∃ s, ∃ (hs : 1 ≤ s), s ≤ k ∧
  ∃ a : ℕ → ℕ,
  a s ≥ s ∧
  StrictMonoOn a (Finset.Icc s k) ∧
  m = ∑ i in Finset.Icc s k, Nat.choose (a i) i :=
  by
  sorry

#check Nat.sub_eq_iff_eq_add
#check Finset.max'
-- s = (Finset.range m+1).filter (fun x => Nat.choose x k ≤ m)
-- 1 is in s
-- da k ≥ 1, Nat.choose x k ≥ x, by x ≥ m+1, is  Nat.choose x k > m
/--Die Menge a_k max ist nicht leer--/
lemma cascade_ne (m k: ℕ ) (hm : 1 ≤ m):
  ((Finset.range (m+1)).filter (fun x => Nat.choose x k ≤ m)).Nonempty :=
  by
  use 1
  simp only [Finset.mem_filter, Finset.mem_range, lt_add_iff_pos_left]
  constructor
  · apply Nat.le_trans hm
    apply Nat.le_refl
  · have choose_one_left (l : ℕ ) : (Nat.choose 1 l) ≤ 1 :=
      by
      induction' l with l ld
      · rw[Nat.choose_zero_right]
      · rw[Nat.choose_succ_right]
        · simp only [tsub_self, Nat.choose_zero_succ, add_zero]
          cases' l with l
          · rw[Nat.choose]
          · rw[Nat.choose_zero_succ]
            decide
        · decide
    specialize choose_one_left k
    apply Nat.le_trans choose_one_left
    exact hm


#check Nat.choose_succ_right
#check Nat.choose_eq_zero_iff
#check Nat.choose_succ_right

#eval Nat.choose 20 0

#check Nat.choose_one_right
#check Nat.choose_zero
