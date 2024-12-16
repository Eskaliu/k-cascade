--help10
import Mathlib
open BigOperators
def a_k_candidates (k m : Nat) : Finset Nat :=
  (Finset.range (max (m+1) (k+1))).filter (fun x => Nat.choose x k ≤ m)

  
#check StrictMonoOn
lemma ref_5(k m : Nat) (hm : 1 ≤ m) :(a_k_candidates k m).Nonempty :=
  by
  use 0
  rw[a_k_candidates]
  rw[Finset.mem_filter]
  rw[Finset.mem_range]
  constructor
  · rw [lt_max_iff]
    left
    exact Nat.add_pos_left hm 1
  · by_cases hk : k = 0
    · rw [hk]
      rw [Nat.choose]
      exact hm
    · simp_rw [Nat.ne_zero_iff_zero_lt] at hk
      --have n_lt_k
      rw [← Nat.choose_eq_zero_iff] at hk
      rw [hk]
      exact Nat.zero_le m
      
#check Nat.choose_le_choose
def a_k (k m : Nat) (hm : 1 ≤ m) : Nat :=
  Finset.max' (a_k_candidates k m) (ref_5 k m hm)  -- ref 5 ist der Beweis, dafür dass a_k_candidates keine leere Liste ist und somit ein Max besitzt.

lemma a_k_prop (k m : Nat) (hm : 1 ≤ m) : Nat.choose (a_k k m hm) k ≤ m :=
  by
  --rw[a_k]
  
  sorry
lemma help_11 (k : ℕ)
(q1 : 1 ≤ k)
(m : ℕ)
(hm : 1 ≤ m)
(s : ℕ)
(a : ℕ → ℕ)
(q : 1 ≤ ∑ i ∈ Finset.Icc s k, (a i).choose i)
(t : 1 ≤ s)
(u : s ≤ k)
(left : StrictMonoOn a (Set.Icc s k))
(left_1 : s ≤ a s)
(right : m - (a_k (k + 1) m hm).choose (k + 1) = ∑ i ∈ Finset.Icc s k, (a i).choose i) :
a k < a_k (k + 1) m hm := 
by
by_contra! contra /-
have contra_succ : a k ≤ a (k+1) := 
  by 
  
  sorry-/ 
have sum_ge_ak : ∑ i ∈ Finset.Icc s k, (a i).choose i + (a_k (k + 1) m hm).choose (k + 1) ≥ (a k).choose k + (a_k (k + 1) m hm).choose (k + 1) := 
  by 
  have sum_ge_ak_help :  ∑ i ∈ Finset.Icc s k, (a i).choose i ≥(a k).choose k := 
    by 
    simp only [ge_iff_le]
    have ge_zero {i : Nat} (h : i ∈ Finset.Icc s k) : 0 ≤ (fun i => (a i).choose i) i := 
    by
      exact Nat.zero_le ((a i).choose i)
    
    apply @Finset.single_le_sum _ _ _ (fun i => (a i).choose i) (Finset.Icc s k) (by apply ge_zero ) _
    rw [Finset.mem_Icc]
    simp_all only [Finset.mem_Icc, zero_le, implies_true, le_refl, and_self] --(Finset.exists_le_maximal)
    
  rel [sum_ge_ak_help]
  

have helpi : (a k).choose k + (a_k (k + 1) m hm).choose (k + 1) ≥ (a_k k m hm).choose k + (a_k (k + 1) m hm).choose (k + 1):= 
  by
  simp only [ge_iff_le]
  apply Nat.eq_add_of_sub_eq at right
  have helpj: (a_k k m hm).choose k ≤ (a k).choose k := 
    by 
    have choose_le_succ : Nat.choose (a_k (k) m hm) k ≤  Nat.choose (a_k (k + 1) m hm) k:= 
      by
      --simp_rw [StrictMonoOn] at left
      apply Nat.choose_le_choose
      repeat rw[a_k]
      refine Finset.max'_subset (ref_5 k m hm) ?_
      repeat rw[a_k_candidates]
      induction' k with k kd
      · simp only [Nat.choose_zero_right, zero_add, le_add_iff_nonneg_left, zero_le,
        sup_of_le_left, Finset.filter_const, Nat.choose_one_right, Nat.reduceAdd]
        rw[if_pos hm]
        
        have helper : Finset.filter (fun x => x ≤ m) (Finset.range (m + 1)) ⊆ Finset.filter (fun x => x ≤ m) (Finset.range ((m + 1) ⊔ 2)):=
          by
          refine Finset.filter_subset_filter (fun x => x ≤ m) ?_
          refine GCongr.finset_range_subset_of_le ?_
          exact Nat.le_max_left (m + 1) 2

        have helpet : (Finset.filter (fun x => x ≤ m) (Finset.range (m + 1)))= Finset.range (m + 1) :=
            by 
              induction' m with m md
              · simp only [nonpos_iff_eq_zero, zero_add, Finset.range_one]
                rfl
              · simp only [zero_add, Nat.choose_one_right, Nat.choose_zero_right, ge_iff_le,
                add_le_add_iff_right] at md
                simp only [zero_add] at contra
                simp only [nonpos_iff_eq_zero, one_ne_zero] at *  
        
        have helpes : Finset.range (m + 1) ⊆ Finset.filter (fun x => x ≤ m) (Finset.range (m + 1)) := by rw [helpet]  
        apply Finset.Subset.trans helpes
        apply Finset.Subset.trans helper
        simp only [subset_refl]
        
      · simp only [ge_iff_le, add_le_add_iff_right] at kd
        by_cases kas:k=0
        · rw [kas] at kd
          repeat rw [kas]
          simp only [le_add_iff_nonneg_left, zero_le, ge_iff_le, add_le_add_iff_right,
            nonpos_iff_eq_zero, one_ne_zero, zero_add, Nat.choose_zero_right, Nat.choose_one_right,
            sup_of_le_left, Finset.filter_const, Nat.reduceAdd, IsEmpty.forall_iff] at *
          have max_2_msucc : max (m+1) 2 = m+1 := 
            by 
            simp only [sup_eq_left, Nat.reduceLeDiff]   
            exact hm
          
          simp_rw [max_2_msucc]
          induction' m with m mad
          · simp only [zero_add, Nat.one_le_ofNat, sup_of_le_right, OfNat.ofNat_ne_one] at *
          · simp only [sup_eq_left, Nat.reduceLeDiff, le_add_iff_nonneg_left, zero_le,
            sup_of_le_left] at mad
            have max3 : max (m+1+1) 3= m+1+1 := 
              by 
              simp only [sup_eq_left, Nat.reduceLeDiff]
              
              sorry
            
            sorry
        · sorry
    sorry

  rel [helpj]  
  sorry

have helpk : (a_k k m hm).choose k + (a_k k m hm).choose (k + 1) = (a_k k m hm + 1).choose (k+1) := 
  by 
  rw [Nat.choose_succ_succ]

have m_ge : m ≥ (a_k k m hm + 1).choose k := 
  by
  
  simp only [ge_iff_le]
  
  sorry

  
· sorry
  






#exit
#check Nat.eq_add_of_sub_eq
/-- Buch: If a (k-1) ≥ a k, then we would ...
  -- bei uns k → k+1 und k-1 → k


/-- Beweist: (∑ i=0 -> n + 1)  =  (∑ i=0 -> n) + n+1 --/
lemma help_10 (k : ℕ)
(q1 : 1 ≤ k)
(m : ℕ)
(hm : 1 ≤ m)
(s : ℕ)
(a : ℕ → ℕ)
(q : 1 ≤ ∑ i ∈ Finset.Icc s k, (a i).choose i)
(t : 1 ≤ s)
(u : s ≤ k)
(left : StrictMonoOn a (Set.Icc s k))
(left_1 : s ≤ a s)
(right : m - (a_k (k + 1) m hm).choose (k + 1) = ∑ i ∈ Finset.Icc s k, (a i).choose i)
(x : ℕ)
(hx : x ∈ Set.Icc s (k + 1))
(y : ℕ)
(hy : y ∈ Set.Icc s (k + 1))
(x_le_y : x < y)
(q2 : x ≤ k)
(q3 : k < y)
(x_lt_ksucc : x < k + 1)
(lelem4 : x ∈ Set.Icc s k):
a x < a_k (k + 1) m hm := 
by 
rw [le_iff_eq_or_lt] at q2
cases' q2 with q2 q2
· rw [q2]
  apply help_11 
  
  all_goals sorry
· apply @lt_trans _ _ _ (a k) _
  · rw [StrictMonoOn] at left
    apply left 
    · sorry
    · sorry
    · sorry

  · --help11
    sorry




  #exit
    --simp_all only [Set.mem_Icc, and_self]
    --obtain ⟨left_2, right_1⟩ := hx
    --obtain ⟨left_3, right_2⟩ := hy
    have lelem1 :x ∈ Set.Icc s k := 
                      by 
                      rw[Set.mem_Icc]
                      constructor
                      · rw[Set.mem_Icc] at hx
                        exact hx.left
                      · exact q2
    have lelem3 :y ∈ Set.Icc s k := 
                      by 
                      rw[Set.mem_Icc]
                      constructor
                      · rw[Set.mem_Icc] at hx
                        exact hy.left
                      · simp_all only [Set.mem_Icc, and_self]
                        obtain ⟨left_2, right_1⟩ := hx
                        obtain ⟨left_3, right_2⟩ := hy
                      
                        have y_lt_ksucc : y < k.succ := 
                          by 
                            rw [Nat.succ_eq_add_one]
                            have le_of_lt_ : k+1 ≤ y := by exact q3 
                            refine Nat.lt_add_right 1 ?_
                            
                            --apply Nat.
                            
                            
                            
                            
                            by_cases yt : y = k+1
                            · rw [yt]
                              simp only [lt_self_iff_false]
                              subst yt
                              simp_all only [lt_add_iff_pos_right, zero_lt_one, le_refl]
                              rw [← Nat.le_succ] at left_3
                              sorry
                            · sorry
                        -- y < k+1 => y ≤ k
                        refine Nat.le_of_lt_succ (y_lt_ksucc)
                        
                        

    specialize @left x lelem1
    
    sorry



  --help10
