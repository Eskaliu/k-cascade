import Mathlib
open BigOperators
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

--#check lt_max_iff
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
/- #check Finset.Icc_eq_cons_Ico
#check Finset.sum_cons
 -/

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

--#check max_le_iff



--#check Nat.eq_add_of_sub_eq
-- a = m ; b = a_k ... ; c = 0
-- hle mit


-- das gefundene Max Elem erfuellt die Eingeschaft ≤ m 
lemma a_k_prop (k m : Nat) (hm : 1 ≤ m) : Nat.choose (a_k k m hm) k ≤ m :=
  by
  have := Finset.max'_mem _ (ref_5 k m hm)
  unfold a_k
  dsimp [a_k_candidates] at *
  rw [Finset.mem_filter] at this
  exact this.2 
#check Finset.mem_filter
-- Zeigt max ist in Menge enthalten
--#check Finset.max'_mem

--beweist, dass a k < a_k+1 (jedes Element aₖ ∈ [s,k] ist natürlich streng kleiner als das Maximum von der Folge a welche über [s,k+1] läuft)
lemma help_11 (k : ℕ)
(q1 : 1 ≤ k)
(m : ℕ)
(hm : 1 ≤ m)
(s : ℕ)
(a : ℕ → ℕ)
(q : 1 ≤ ∑ i ∈ Finset.Icc s k, (a i).choose i)
(t : 1 ≤ s)
(u : s ≤ k)
(mono : StrictMonoOn a (Set.Icc s k))
(mono_1 : s ≤ a s)
(right : m - (a_k (k + 1) m hm).choose (k + 1) = ∑ i ∈ Finset.Icc s k, (a i).choose i) :
a k < a_k (k + 1) m hm := 
by
--Beweis per Widerspruch
--Contra ist die negierte Aussage welche wir beweisen möchte
by_contra! contra
replace right := Nat.eq_add_of_sub_eq (a_k_prop (k+1) m hm) right
have sum_ge_ak : ∑ i ∈ Finset.Icc s k, (a i).choose i + (a_k (k + 1) m hm).choose (k + 1) ≥ (a k).choose k + (a_k (k + 1) m hm).choose (k + 1) := 
  by 
  apply Nat.add_le_add_right
  have : ∑ i ∈ Finset.Icc k k, (a i).choose i ≤ ∑ i ∈ Finset.Icc s k, (a i).choose i :=
    by
    apply Finset.sum_le_sum_of_subset
    apply Finset.Icc_subset_Icc u (le_refl _)
  rw [Finset.Icc_self, Finset.sum_singleton] at this
  exact this
rw [← right] at sum_ge_ak
--widerspruch da .................................................
have toChoose := Nat.choose_mono k contra
dsimp at toChoose
have more := le_trans (Nat.add_le_add_right toChoose _) sum_ge_ak
rw [← Nat.choose_succ_succ] at more
have almost := a_k_maximiser (k+1) m (by exact Nat.le_add_right_of_le q1) hm _ more
linarith

-- (a_k (k + 1) m hm).choose (k + 1) + a k).choose k + (a_k (k + 1) m hm).choose (k + 1) > m weil m = ... ist Beweise ! 
#print Monotone

#check Nat.add_le_add_right


/- 
  --simp only [ge_iff_le]
  have ge_zero {i : Nat} (h : i ∈ Finset.Icc s k) : 0 ≤ (fun i => (a i).choose i) i := 
  by
    exact Nat.zero_le ((a i).choose i)
  
  apply @Finset.single_le_sum _ _ _ (fun i => (a i).choose i) (Finset.Icc s k) (by apply ge_zero ) _
  rw [Finset.mem_Icc]
  simp_all only [Finset.mem_Icc, zero_le, implies_true, le_refl, and_self] --(Finset.exists_le_maximal)
    
  rel [sum_ge_ak_help] -/
#check Nat.eq_add_of_sub_eq
  

#check Finset.sum_le_sum_of_subset
#check Finset.Icc_self

-- Hier steht der Beweis zum k-kaskade Lemma
/--∀m,k ∈ ℕ, 1 ≤ m ∃s: 1 ≤ s ∧ s ≤ k : ∃ Folge mit aₖ ≥ ...≥ aₛ für welches gilt
  m = aₖ choose k + .... + aₛ choose s -/
theorem cascade (k : Nat) (hk : 1 ≤ k) :
  ∀ m : Nat, 1 ≤ m →
  ∃ s : Nat, (1 ≤ s) ∧ (s ≤ k) ∧
    ∃ a :  Nat → Nat, StrictMonoOn a (Finset.Icc s k) ∧ s ≤ a (s) ∧
      m = ∑ i in (Finset.Icc s k), (Nat.choose (a i) i) :=
  by
  --Beweis per Induktion über k 
  induction' k with k ih
  · --Unsere Aussage gilt nich für k=0 also haben wir einen Widerspruch
    contradiction
  · by_cases q1 : 1 ≤ k
    --Case 1 ≤ k
    · -- da die Voraussetzung für ih in q1 vorhanden ist können wir die Implikation der Aussage nutzen
      specialize ih q1
      --führe die Aussage m und hm ein (m: m ∈ ℕ ) (hm: 1 ≤ m )
      intro m hm
      simp
      /-Hier haben wir einen kleinen Unterschied zum händischen Beweis, um uns die Arbeit zu vereinfach nutzen wir direkt 
       m - a_k choose k+1
       und betrachen die Fälle = 0 und ≠ 0  
      -/
      specialize ih (m - (Nat.choose (a_k (k+1) (m) hm) (k+1)))
      by_cases q : m - (a_k (k + 1) m hm).choose (k+1) = 0
      --Fall 1: m - a_k choose k+1 = 0 
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
                rw [Nat.sub_eq_zero_iff_le] at q
                apply le_antisymm q
                apply a_k_prop

                
        --Fall2 : m - a_k choose k+1 ≠ 0       
      · simp_rw [← Nat.one_le_iff_ne_zero] at q
        specialize ih q
        --wir obtain'en die einzelnen Aussagen ...
        obtain ⟨s,hs⟩ := ih
        obtain ⟨t,ks⟩ := hs
        obtain ⟨u,ts⟩ := ks
        obtain ⟨a,more⟩ := ts
        --... setzen für s s ein
        use s
        -- damit wir dann die Konjunktion mit Constructor auseinander nehmen können um, die Teilaussagen einzeln zu beweisen.
        constructor
        -- 1 ≤ s folgt direkt aus Aussage t
        · exact t
        --noch einmal auseinandernehmen der Konjunktion mit Constructor
        · constructor
          · simp_all only [le_add_iff_nonneg_left, zero_le, Finset.coe_Icc]
            obtain ⟨mono, right⟩ := more
            obtain ⟨mono_1, right⟩ := right
            exact Nat.le_add_right_of_le u
          · use (fun x => if x ≤ k then a x else (a_k (k+1) m hm))
            constructor 
            · simp_all only [le_add_iff_nonneg_left, zero_le, Finset.coe_Icc]
              obtain ⟨mono, right⟩ := more
              obtain ⟨mono_1, right⟩ := right
              intro x hx y hy x_le_y
              dsimp
              --Fallunterscheidung für x in Bezug auf k 
              by_cases q2: x ≤ k
              --Fall 1 : x ≤ k 
              · rw [if_pos q2]
                --Fallunterscheidung für y in Bezug auf k
                by_cases q3: y ≤ k
                --Fall 1 : y ≤ k
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
                  specialize @mono x lelem2 y lelem3 x_le_y
                  exact mono
                --Fall 2: y > k
                · rw [if_neg q3]
                  rw [not_le] at q3
                  have x_lt_ksucc : x < k + 1 := 
                    by
                    exact Order.lt_add_one_iff.mpr q2
                  --lelem4 sagt aus das x ∈ [s,k] 
                  have lelem4 :x ∈ Set.Icc s k := 
                    by 
                    rw[Set.mem_Icc]
                    constructor
                    · rw[Set.mem_Icc] at hx
                      exact hx.left
                    · exact q2
                  rw [Nat.le_iff_lt_or_eq] at q2
                  --betrachte die Faelle fuer x < k und x = k  
                  cases' q2 with q2 q2
                  --Fall 1 : x < k
                  · apply @Nat.lt_of_lt_of_le _ (a k)
                    · apply mono
                      exact lelem4  
                      · exact Set.right_mem_Icc.mpr u
                      · exact q2
                    · --zeige a(k) ≤ a_k (k + 1)
                      apply le_of_lt
                      apply help_11 k q1 m hm s a q t u mono mono_1 right 
                  --Fall2: x = k 
                  · rw [q2]
                    apply help_11 k q1 m hm s a q t u mono mono_1 right 
                    --apply help_11
              --Fall 2 x > k 
              · rw [if_neg q2]
                by_cases q4: y ≤ k
                · --Fall 1 : y ≤ k
                  rw [if_pos q4]
                  simp only [not_le] at q2  
                  exfalso
                  apply lt_irrefl k
                  apply lt_trans q2
                  apply lt_of_lt_of_le x_le_y q4
                  --Fall 2: y > k
                · rw [if_neg q4]
                  rw [a_k]
                  rw [lt_self_iff_false]
                  simp_all only [Set.mem_Icc, not_le]
                  obtain ⟨mono_2, right_1⟩ := hx
                  obtain ⟨mono_3, right_2⟩ := hy
                  --have y_eq_ksucc : y = k + 1 := by linarith
                  --have x_eq_ksucc : x = k + 1 := by linarith
                  have x_eq_y : x = y := by linarith
                  subst x_eq_y
                  simp_all only [lt_self_iff_false]
            /- Hier noch ein paar Kommentare maybe ---------------------------------------------------------------
             -/
            · constructor
              · -- s ≤ k gilt (Aussage u) 
                rw [if_pos u]
                exact more.2.1
              · rw [icc_succ]
                · rw [if_neg (by exact Nat.not_succ_le_self k)]
                  apply Nat.eq_add_of_sub_eq
                  · apply a_k_prop 
                  · simp_all only [le_add_iff_nonneg_left, zero_le, Finset.coe_Icc]
                    obtain ⟨mono, right⟩ := more
                    obtain ⟨mono_1, right⟩ := right
                    apply Finset.sum_congr rfl
                    intro z zicc
                    rw [Finset.mem_Icc] at zicc
                    rw [if_pos zicc.right]                     
                     
                  
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







#exit
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
