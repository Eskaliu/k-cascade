import Mathlib
open BigOperators
--VERSION MIT MAX @ a_k_candidates
--Filtert die a_k raus, welche <= m sind
def a_k_candidates (k m : Nat) : Finset Nat :=
  (Finset.range (max (m+1) (k+1))).filter (fun x => Nat.choose x k ≤ m)

lemma help_8 (k x : Nat) (hk : 1 ≤ k) (hx: k+1 ≤ x) : x ≤ Nat.choose x k := 
  by
  induction' x with x ihx
  · contradiction
  · rw [le_iff_eq_or_lt] at hx
    cases' hx with hx hx
    · rw [← hx, Nat.choose_succ_self_right]
    · rw [Nat.lt_succ_iff] at hx
      specialize ihx hx
      cases' k with k
      · contradiction
      · rw [Nat.choose_succ_succ']
        rw [add_comm]
        apply add_le_add
        · rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero]
          apply Nat.choose_pos
          apply le_trans _ hx
          linarith
        · exact ihx

/--m+1 ≤ x ⇒ m < x choose k-/
lemma help_7 (k m x : Nat) (hk: 1 ≤ k) (hx : k+1 ≤ x) (hm: m+1 ≤ x): m < Nat.choose x k :=   
  by
  rw [Nat.lt_iff_add_one_le]
  apply Nat.le_trans hm (help_8 _ _ hk hx) 
  
example (h : 0 < x) : Nat.choose 0 x = 0 := by exact Nat.choose_eq_zero_iff.mpr h

/--Beweist, dass die Menge a_k_candidates nie leer sein kann-/
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

#check lt_max_iff
/-- a_k ist die Funktion, welche uns aₖ gibt siehe Beweis des Lemmas -/
def a_k (k m : Nat) (hm : 1 ≤ m) : Nat :=
  Finset.max' (a_k_candidates k m) (ref_5 k m hm)  -- ref 5
/--Beweist: (∑ i=0 -> n + 1)  =  (∑ i=0 -> n) + n+1   --/

lemma icc_eq_ico_cons (a b : Nat) : Finset.Icc a b = Finset.Ico a (b+1) :=
  by exact rfl

lemma icc_succ (s k : Nat) (sk: s ≤ k) (a : Nat → Nat):
∑ i ∈ Finset.Icc s (k+1), (Nat.choose (a i) i)
  = (∑ i ∈ Finset.Icc s k, (Nat.choose (a i) i)) + Nat.choose (a (k + 1)) (k+1):=
  by
  rw [Finset.Icc_eq_cons_Ico]
  · rw [Finset.sum_cons]
    · rw[← icc_eq_ico_cons]
      rw [add_comm]
  · rw [Nat.le_add_one_iff]
    left
    exact sk

--#check Finset.sum_Ico_succ_top
#check Finset.Icc_eq_cons_Ico
#check Finset.sum_cons


-- Zeige kein Binom mit x oben und x>=m ist x uber k > m
-- um Zu beweisen das Finset.max oben auch max findet
lemma a_k_maximiser (k m : Nat) (hk : 1 ≤ k) (hm : 1 ≤ m) : ∀ x , Nat.choose x k ≤ m → x ≤ a_k k m hm :=
  by
  intro x hx 
  by_cases q1 : x ∈ a_k_candidates k m
  · rw [a_k]
    exact Finset.le_max' _ _ q1
  · exfalso
    rw [a_k_candidates, Finset.mem_filter, And.comm] at q1
    simp only [not_and, not_le] at q1
    specialize q1 hx
    simp only [Finset.mem_range, not_lt] at q1
    rw [max_le_iff] at q1
    have name := help_7 k m x hk q1.right q1.left  
    apply not_le_of_lt name
    exact hx

#check max_le_iff



#check Nat.eq_add_of_sub_eq
-- a = m ; b = a_k ... ; c = 0
-- hle mit


-- das gefundene Max Elem erfuellt die Eingeschaft ≤ m 
lemma a_k_prop (k m : Nat) (hm : 1 ≤ m) : Nat.choose (a_k k m hm) k ≤ m :=
  by
  --rw[a_k]

  sorry  
#check Finset.mem_filter
-- Zeigt max ist in Menge enthalten
#check Finset.max'_mem




-- Hier steht der Beweis zum k-kaskade Lemma
/--∀m,k ∈ ℕ, 1 ≤ m ∃s: 1 ≤ s ∧ s ≤ k : ∃ Folge mit aₖ ≥ ...≥ aₛ für welches gilt
  m = aₖ choose k + .... + aₛ choose s -/
theorem cascade (k : Nat) (hk : 1 ≤ k) :
  ∀ m : Nat, 1 ≤ m →
  ∃ s : Nat, (1 ≤ s) ∧ (s ≤ k) ∧
    ∃ a :  Nat → Nat, StrictMonoOn a (Finset.Icc s k) ∧ s ≤ a (s) ∧
      m = ∑ i in (Finset.Icc s k), (Nat.choose (a i) i) :=
  by
  induction' k with k ih
  · contradiction
  · by_cases q1 : 1 ≤ k
    --Case 1 ≤ k
    · specialize ih q1
      intro m hm
      simp
      specialize ih (m - (Nat.choose (a_k (k+1) (m) hm) (k+1)))
      by_cases q : m - (a_k (k + 1) m hm).choose (k+1) = 0
      · use (k+1)
        constructor
        · exact hk
        · constructor
          · simp only [le_refl]
          · use (fun x => if x = (k+1) then (a_k (k+1) m hm) else 0)
            constructor
            --done beweist [k+1, k+1] = {k+1}
            --wir haben den Beweis "eigentlich" schon, aber wir haben die Aussage nur als Äquivalenz
            --Deshalb muessen wir eine Behauptung aufstellen, welche die Aussage als eine Gleichung
            --beweist, damit wir es auf unser Ziel anwenden können.
            · have done : Set.Icc (k + 1) (k + 1) = {k+1} :=
                by
                --Set.Icc_eq_singleton_iff  ist die Äquivalenz von der ich oben gesprochen habe.
                --Set.Icc (k+1) (k+1) => {k+1}
                rw [Set.Icc_eq_singleton_iff]
                -- ∧ ist reflexiv
                simp only [and_self]
              rw [done]
              --[k+1, k+1] = {k+1}
              apply Set.strictMonoOn_singleton
              
            · constructor
              --Beweise k + 1 ≤ a_k(k + 1) m hm
              · simp only [↓reduceIte]
                apply a_k_maximiser
                · exact hk
                · rw [Nat.choose_self]
                  exact hm
              · simp only [Finset.Icc_self, Finset.sum_singleton, add_right_eq_self, one_ne_zero,
                ↓reduceIte, Nat.choose_zero_succ]


                sorry
              
      · simp_rw [← Nat.one_le_iff_ne_zero] at q
        specialize ih q
        --wir obtain'en die einzelnen Aussagen ...
        obtain ⟨s,hs⟩ := ih
        obtain ⟨t,ks⟩ := hs
        obtain ⟨u,ts⟩ := ks
        obtain ⟨a,more⟩ := ts
        --... setzen für s s ein
        use s
        -- damit wir dann die Aussage mit Constructor auseinander nehmen können um, die Teilaussagen einzeln zu beweisen.
        constructor
        -- 1 ≤ s folgt direkt aus Aussage s
        · exact t
        --noch einmal auseinandernehmen einer ∧ Aussage mit Constructor
        · constructor
          · simp_all only [le_add_iff_nonneg_left, zero_le, Finset.coe_Icc]
            obtain ⟨left, right⟩ := more
            obtain ⟨left_1, right⟩ := right
            exact Nat.le_add_right_of_le u
          · use (fun x => if x ≤ k then a x else (a_k (k+1) m hm))
            constructor 
            · simp_all only [le_add_iff_nonneg_left, zero_le, Finset.coe_Icc]
              obtain ⟨left, right⟩ := more
              obtain ⟨left_1, right⟩ := right
              intro x hx y hy x_le_y
              dsimp
              by_cases q2: x ≤ k
              · rw [if_pos q2]
                by_cases q3: y ≤ k
                · rw [if_pos q3]
                  -- Lemma zeige x ∈ Set.Icc s k (s ≤ x ≤ k)
                  have lelem2 :x ∈ Set.Icc s k := 
                    by 
                    rw[Set.mem_Icc]
                    constructor
                    · rw[Set.mem_Icc] at hx
                      exact hx.left
                    · exact q2
                  -- gleiches Lemma für y
                  have lelem3 :y ∈ Set.Icc s k := 
                    by 
                    rw[Set.mem_Icc]
                    constructor
                    · rw[Set.mem_Icc] at hx
                      exact hy.left
                    · exact q3    
                  specialize @left x lelem2 y lelem3 x_le_y
                  exact left

                · rw [if_neg q3]
                  rw [not_le] at q3
                  have x_lt_ksucc : x < k + 1 := 
                    by
                    exact Order.lt_add_one_iff.mpr q2
                  have lelem4 :x ∈ Set.Icc s k := 
                    by 
                    rw[Set.mem_Icc]
                    constructor
                    · rw[Set.mem_Icc] at hx
                      exact hx.left
                    · exact q2
                      
                  --help_10
                  sorry

              · rw [if_neg q2]
                by_cases q4: y ≤ k
                · rw [if_pos q4]
                  simp only [not_le] at q2  
                  
                  sorry
                · rw [if_neg q4]
                  rw [a_k]
                  rw [lt_self_iff_false]
                  simp_all only [Set.mem_Icc, not_le]
                  obtain ⟨left_2, right_1⟩ := hx
                  obtain ⟨left_3, right_2⟩ := hy
                  --have y_eq_ksucc : y = k + 1 := by linarith
                  --have x_eq_ksucc : x = k + 1 := by linarith
                  have x_eq_y : x = y := by linarith
                  subst x_eq_y
                  simp_all only [lt_self_iff_false]
            · constructor
              · sorry
              · rw [icc_succ]
                · sorry
                · exact u
              


      -- Fall 1 > k ==> k = 0 (da k ∈ ℕ )
    · simp only [not_le, Nat.lt_one_iff] at q1
      rw [q1]
      intro m hm
      use 1
      refine' ⟨le_refl 1, le_refl 1, _ ⟩
      use (fun n => if n = 1 then m else 0)
      constructor
      · rw[Finset.Icc_self]
        simp only [Finset.coe_singleton, Set.strictMonoOn_singleton] -- ref_2
      · constructor
        · simp only [↓reduceIte]
          exact hm -- ref_3
        · simp only [zero_add, Finset.Icc_self, Finset.sum_singleton, ↓reduceIte,
          Nat.choose_one_right] -- ref_4

#check Set.Icc_eq_singleton_iff

-- # ref_3

#check if_pos

-- # ref_2 ref_4

#check Finset.Icc_self
#check Set.strictMonoOn_singleton
#check Finset.sum_singleton
#check if_pos
#check Nat.choose_one_right


lemma help_maxi (k m x: ℕ ) (hm : 1 ≤ m) : x < m + 1 → m < x.choose k :=
  by
  induction' m with m md
  · intro a
    simp_all only [nonpos_iff_eq_zero, one_ne_zero]
  · intro a
    
    sorry


-- # ref_7

-- kann `x` in `Finset.range (m+1)` sein ?
#check Finset.mem_filter

-- anschließend als ungleichung azsdrücken, mit
#check Finset.mem_range

-- dann help_7

-- mit
#check Nat.lt_iff_add_one_le
#check Nat.choose_succ_self_right
#check Nat.choose_le_choose

-- abschließen mit
#check Nat.not_le_of_lt
#check False.elim
-- oder bei letzterem di tactic `exfalso`

#check False.elim

#check not_le_of_lt

--Im Hauptbeweis können 2 Fälle passieren, laut
#check le_iff_eq_or_lt

-- Im Fall von = können wir s := (k+1) und a := (fun x => if x = (k+1) then (a_k (k+1) m sorry) else 0)
-- setzen und schnell fertig sein
-- Adernfalls können wir ↓ nutzen
#check Nat.sub_pos_iff_lt
#check Nat.lt_iff_add_one_le
-- und erhalten dass `1 ≤ m - (Nat.choose (a_k (k+1) m sorry) (k+1))`

-- Bennen wir `1 ≤ m - (Nat.choose (a_k (k+1) m sorry) (k+1))` *dif*
-- und merken dass man `ih` in *dif* spezialisieren kann
-- Dann gibt `ih` uns ein `s` und eine sequenz `a` (die aber nur auf [s,k] monoton ist, nicht [s,(k+1)])
-- und die Tatsache dass `m - (Nat.choose (a_k (k+1) m sorry) (k+1)) = ∑ i ∈ [s,k], Nat.choose ...`

-- Wir wollen dieses `s` nutzen, und die sequenz erweitern durch:
-- A := `fun x => if x ≤ k then a x else (a_k (k+1) m sorry)`
-- Dann, mit der vorherigen gleichung und:
-- `(Nat.choose (a_k (k+1) m sorry) (k+1)) + (∑ i ∈ [s,k], Nat.choose (a i) i) = ∑ i ∈ [s,(k+1)], Nat.choose (A i) i`
-- (welches wir beweisen müssen), hätten wir unsere gewünschte cascade darstellung für k+1

-- Außerdem muss dann bewiesen werden dass `A k < A (k+1)` für die stricte monotonie
-- Das lemma das im Buch genutz wird ist
#check Nat.choose_succ_succ
-- und sein "contradcitig maximality of aₖ" ist unser lemma "a_k_maximiser" und
#check Nat.not_succ_le_self
-- # ref_5

-- use 0, dann
#check Finset.mem_filter
#check Finset.mem_range
#check Nat.zero_le
-- cases' auf k, dann
#check Nat.choose_zero_right
#check Nat.choose_zero_succ

-- # ref_6
#check Finset.le_max'

