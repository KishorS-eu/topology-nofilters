/-
how to make this better?
- split project into multiple files
- reorganise the nbhd definitions
- rename project
- sort out formatting
-/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set

structure topology (X : Type) where
/-
struct defining topologies on a set X
  · defines openness
  · X and empty set are open
  · open intersection and union
-/
  isOpen : Set X → Prop
  univOpen : isOpen (univ : Set X)
  emptyOpen : isOpen (∅ : Set X)
  interOpen : ∀ s t, isOpen s → isOpen t → isOpen (s ∩ t)
  unionOpen : ∀ s, (∀ t ∈ s, isOpen t) → isOpen (⋃₀ s)

variable (X : Type) (τ : topology X)

-- basics

def isOpen (x : Set X) : Prop :=
  τ.isOpen x 

theorem univOpen : isOpen (X : Type) (τ : topology X) (univ : Set X) := by
  apply τ.univOpen

theorem emptyOpen : isOpen (X : Type) (τ : topology X) (∅ : Set X) := by
  apply τ.emptyOpen

theorem interOpen (x y : Set X) (hx : isOpen X τ x) (hy : isOpen X τ y) : isOpen X τ (x ∩ y) := by
  apply τ.interOpen
  apply hx
  apply hy

theorem unionOpen (B : Set (Set X)) (h : ∀ b ∈ B, isOpen X τ b) : isOpen X τ (⋃₀ B) := by
  apply τ.unionOpen
  apply h

-- neighbourhoods

def nbhd (U : Set X) (x : X) : Prop :=
  x ∈ U ∧ isOpen X τ U

theorem open_imp_nbhd (U : Set X) (h : isOpen X τ U) : ∀ u ∈ U, ∃ G : Set X, nbhd X τ G u := by
  intro u hU
  use U
  rw [nbhd]

  constructor
  apply hU
  apply h

-- converse seems to be more difficult though :(

theorem nbhd_imp_open (U : Set X) (H : Set (Set X)) (h1 : ∀ G ∈ H, G ⊆ U) (h2 : ∀ G ∈ H, ∃ u ∈ U, nbhd X τ G u) (h3 : ∀ u ∈ U, ∃ G ∈ H, nbhd X τ G u) : isOpen X τ U := by
  -- NTS: union of neighbourhoods of points in U is U 
  have h4 : U = ⋃₀ H := by
    -- split into two cases
    apply Subset.antisymm
    -- ⊆ direction
    intro x hx
    apply h3 at hx
    cases' hx with y hy
    cases' hy with z hz
    rw [nbhd] at hz
    cases' hz with l r
    exact mem_sUnion_of_mem l z
    -- ⊇ direction
    intro x hx
    rw [mem_sUnion] at hx
    cases' hx with y hy
    cases' hy with hl hr
    exact h1 y hl hr
  -- NTS: Every set in H is open
  have h5 : ∀ G ∈ H, isOpen X τ G := by
    intro G hG
    apply h2 at hG
    cases' hG with w hw
    cases' hw with l r 
    rw [nbhd] at r
    cases' r with irr goal
    exact goal
  rw [h4]
  exact unionOpen X τ H h5

-- interior points

def int_point (U : Set X) (x : X) : Prop :=
  x ∈ U ∧ ∃ G ⊆ U, nbhd X τ G x

def interior_set (U : Set X) (intU : Set X) : Prop :=
  (∀ u ∈ U, int_point X τ U u → u ∈ intU) ∧ (∀ x ∈ intU, int_point X τ U x)

/-
need to show
  S ⊆ T → intS ⊆ intT
  S open ↔ S = intS
-/

theorem interior_set_is_subset (S intS : Set X) (h : interior_set X τ S intS) : intS ⊆ S := by
-- This theorem is defined as it is important for future proofs
  intro x hx
  rw [interior_set] at h
  cases' h with irr1 h1
  specialize h1 x
  apply h1 at hx
  rw [int_point] at hx
  cases' hx with h2 irr2
  exact h2

theorem interior_set_largest (S intS V : Set X) (h1 : interior_set X τ S intS) (h2 : ∀ v ∈ V, int_point X τ S v) : V ⊆ intS := by
-- This theorem ties up the maximality condition in the definition of an interior of a set
  rw [interior_set] at h1
  cases' h1 with hl hr
  intro x h3

  have h4 : V ⊆ S := by
    intro v hV
    specialize h2 v
    rw [int_point] at h2
    apply h2 at hV
    cases' hV with hl hr
    exact hl
  
  rw [subset_def] at h4
  specialize h4 x
  exact hl x (h4 h3) (h2 x h3)

theorem subset_imp_intsubset (S T intS intT : Set X) (h1 : interior_set X τ S intS) (h2 : interior_set X τ T intT) : S ⊆ T → intS ⊆ intT := by
  intro h3 x hx
  rw [subset_def] at h3
  rw [interior_set] at h1 h2 

  have h4 : int_point X τ S x := by
-- NTS: x is interior point of S
    cases' h1 with irr1 goal1
    specialize goal1 x
    apply goal1 at hx
    exact hx
-- NTS: intS ⊆ T
  have h5 : intS ⊆ T := by
    intro y hy
    cases' h1 with l1 r1
    specialize r1 y
    apply r1 at hy
    rw [int_point] at hy
    cases' hy with l2 r2
    apply h3 at l2
    exact l2
-- the goal is split into 3, 2 of which are trivial from hypothesis
  apply interior_set_largest X τ T intT intS
-- Goal 1
  exact h2
-- Goal 2
  intro z hz
  cases' h1 with l1 r1
  specialize r1 z
  apply r1 at hz
  rw [int_point] at hz

  cases' hz with l2 r2
  cases' r2 with G hG
  cases' hG with hGL hGR
  rw [nbhd] at hGR
  cases' hGR with zMem GOpen
-- subgoal
  have GsubT : G ⊆ T := by
-- NTS: subset derived from defintion of an interior point is also a subset of T
    exact fun ⦃a⦄ a_1 ↦ h3 a (hGL a_1)
  rw [int_point]
  specialize h3 z
-- 2nd goal is split into two
  constructor
-- Goal 2.1
  apply h3
  exact l2
-- Goal 2.2
  use G
-- Goal 2.2 is split 2 more times, but these splits are to handle the 'and' statements in the goal
  constructor
  exact GsubT
  
  rw [nbhd]

  constructor
  exact zMem
  exact GOpen
-- Goal 3
  exact hx

theorem set_open_imp_equal_intset (S intS : Set X) (h : interior_set X τ S intS) : isOpen X τ S → intS = S := by
  rw [interior_set] at h
  intro openS
-- we split the goal into proving intS ⊆ S and S ⊆ intS
  apply Subset.antisymm
-- Goal 1
  exact interior_set_is_subset X τ S intS h
-- Goal 2
  rw [subset_def]
  intro x hx

  have all_pts_intpts : ∀ x ∈ S, int_point X τ S x := by
-- this is an equivalent statement to the proof; defined a separate hypothesis as it seemed intuitive to do so
    intro y hy
    rw [int_point]

    constructor
    exact hy

    use S

    constructor
    trivial

    rw [nbhd]

    constructor
    exact hy

    exact openS

  cases' h with maxS intptS
  specialize maxS x
  apply maxS
  exact hx

  specialize all_pts_intpts x
  apply all_pts_intpts at hx
  exact hx

-- PROJECT 2 STARTS HERE

-- redoing the nbhd implies open, without extra hypothesis

theorem nbhd_imp_open_2 (A : Set X) (h : ∀ a ∈ A, ∃ G ⊆ A, nbhd X τ G a) : isOpen X τ A := by
  let H := {G | G ⊆ A ∧ ∃ a ∈ A, nbhd X τ G a}
  have H3 : ∀ a ∈ A, ∃ G ∈ H, nbhd X τ G a := by
    intro a hA
    have a_mem_A := hA
    specialize h a
    apply h at hA
    cases' hA with Gₐ hGₐ
    use Gₐ
    cases' hGₐ with subGₐ nbhdGₐ

    constructor
    rw [@mem_setOf]

    constructor
    exact subGₐ

    use a

    exact nbhdGₐ

  have H1 : ∀ G ∈ H, G ⊆ A := by
    intro G G_mem_H
    rw [@mem_setOf] at G_mem_H
    cases' G_mem_H with G_sub_A G_nbhd
    exact G_sub_A

  have H2 : ∀ G ∈ H, ∃ a ∈ A, nbhd X τ G a := by
    intro G G_mem_H
    rw [@mem_setOf] at G_mem_H
    cases' G_mem_H with G_sub_A G_nbhd
    exact G_nbhd
  exact nbhd_imp_open X τ A H H1 H2 H3

-- ok so this version is definitely better, and can prove the other direction of previous statement from here

theorem equal_intset_imp_open (S intS : Set X) (h : interior_set X τ S intS) : S = intS → isOpen X τ S := by
  intro eqS
  rw [eqS]
  cases' h with maxS intptS
  refine nbhd_imp_open_2 X τ intS ?_
  intro s s_mem_intS
  have hs := s_mem_intS
  specialize intptS s
  apply intptS at hs
  rw [int_point] at hs
  cases' hs with sMem goal
  rw [eqS] at goal
  exact goal

-- convergence

def Hausdorff (X : Type) (τ : topology X) : Prop :=
  ∀ x y : X, x ≠ y → ∃ U : Set X, nbhd X τ U x ∧ ∃ V : Set X, nbhd X τ V y ∧ U ∩ V = ∅

def seq_limit (x : X) (seq : ℕ → X) : Prop :=
  ∀ G : Set X, nbhd X τ G x → ∃ N : ℕ, ∀ n ≥ N, (seq n) ∈ G

def convergent_seq (seq : ℕ → X) : Prop :=
  ∃ x : X, seq_limit X τ x seq


theorem uniq_lims_hausdorff (seq_x : ℕ → X) (h1 : Hausdorff X τ) (h2 : convergent_seq X τ seq_x) : ∃ x : X, seq_limit X τ x seq_x →
                            ∀ y : X, seq_limit X τ y seq_x → x = y := by
  rw [convergent_seq] at h2
  cases' h2 with x h_xlimx
  use x
  intro hP
  intro y h_ylimx
  rw [Hausdorff] at h1
  by_contra x_neq_y
  push_neg at x_neq_y
  specialize h1 x y
  apply h1 at x_neq_y

-- breaking down hausdorff statement
  cases' x_neq_y with U r1
  cases' r1 with nbhdU r2
  cases' r2 with V r3
  cases' r3 with nbhdV int_empty
  
  rw [seq_limit] at *
  specialize h_xlimx U
  apply h_xlimx at nbhdU
  cases' nbhdU with N1 hN1

  specialize h_ylimx V
  apply h_ylimx at nbhdV
  cases' nbhdV with N2 hN2

  let maxN := max N1 N2
  have hMaxN1 : maxN ≥ N1 := by exact Nat.le_max_left N1 N2
  have hMaxN2 : maxN ≥ N2 := by exact Nat.le_max_right N1 N2
  
  specialize hN1 maxN
  apply hN1 at hMaxN1

  specialize hN2 maxN
  apply hN2 at hMaxN2

  have int_nonempty : seq_x maxN ∈ U ∩ V := by exact mem_inter hMaxN1 hMaxN2
  rw [int_empty] at int_nonempty
  
  exact int_nonempty

-- closed sets

def isClosed (X : Type) (τ : topology X) (V : Set X) : Prop :=
  isOpen X τ Vᶜ

theorem emptyClosed : isClosed X τ (∅ : Set X) := by
  rw [isClosed]
  simp
  exact univOpen X τ
  
theorem univClosed : isClosed X τ (univ : Set X) := by
  rw [isClosed]
  simp
  exact emptyOpen X τ

theorem intClosed (B : Set (Set X)) (h : ∀ b ∈ B, isClosed X τ b) : isClosed X τ (⋂₀ B) := by
  let C := {c | ∃ b ∈ B, c = bᶜ}
  have C_isOpen : isOpen X τ (⋃₀ C) := by
    refine unionOpen X τ C ?_
    intro c hc
    rw [@mem_setOf] at hc
    cases' hc with w hw
    cases' hw with mem_w eq_w
    specialize h w
    apply h at mem_w
    rw [isClosed] at mem_w
    rw [← eq_w] at mem_w
    exact mem_w
  rw [isClosed]
  rw [@compl_sInter]
  rw [@sUnion_image]
  rw [@sUnion_eq_biUnion] at C_isOpen 
  have C_eq_B : ⋃ c ∈ C, c = ⋃ b ∈ B, bᶜ := by
    ext x
    constructor
    · intro hc
      rw [← @sUnion_eq_biUnion] at hc
      rw [@mem_sUnion] at hc
      cases' hc with w right
      cases' right with w_mem_c x_mem_w
      rw [@mem_setOf] at w_mem_c
      cases' w_mem_c with b right
      cases' right with left w_comp_b
      rw [w_comp_b] at x_mem_w
      exact mem_biUnion left x_mem_w
    · intro hb
      rw [← @sUnion_eq_biUnion]
      rw [@mem_sUnion]
      rw [@mem_iUnion₂] at hb
      cases' hb with w hw
      cases' hw with w_mem_b x_mem_compw
      use wᶜ
      constructor
      · rw [@mem_setOf]
        use w
      · exact x_mem_compw
  rw [← C_eq_B]
  exact C_isOpen

theorem unionClosed (A B : Set X) (hA : isClosed X τ A) (hB : isClosed X τ B) : isClosed X τ (A ∪ B) := by
  rw [isClosed] at *
  rw [@compl_union]
  exact interOpen X τ Aᶜ Bᶜ hA hB

theorem singleton_hausdorff_closed (a : X) (h : Hausdorff X τ) (A : Set X) (hA1 : a ∈ A) (hA2 : ∀ x ∈ A, x = a) : isClosed X τ A := by
  rw [Hausdorff] at h
  rw [isClosed]
  have compA_contains_nbhds : ∀ b ∈ Aᶜ, ∃ G ⊆ Aᶜ, nbhd X τ G b := by
    intro b hb
    specialize h a b
    rw [@mem_compl_iff] at hb
    have a_neq_b : a ≠ b := by
      exact ne_of_mem_of_not_mem hA1 hb
    apply h at a_neq_b

    cases' a_neq_b with U r1
    cases' r1 with nbhdU r2
    cases' r2 with V r3
    cases' r3 with nbhdV emptyInt
    use V

    constructor
    · rw [subset_def]
      intro v hv
      by_contra v_nMem_compA
      rw [@not_mem_compl_iff] at v_nMem_compA
      have v_memU : v ∈ U := by
        apply hA2 at v_nMem_compA
        rw [nbhd] at nbhdU
        cases' nbhdU with memU isOpenU
        exact mem_of_eq_of_mem v_nMem_compA memU
      have nonemptyInt : v ∈ U ∩ V := by
        exact mem_inter v_memU hv
      rw [@eq_empty_iff_forall_not_mem] at emptyInt
      exact emptyInt v nonemptyInt
    · exact nbhdV
  exact nbhd_imp_open_2 X τ Aᶜ compA_contains_nbhds

-- limit points and closure

def isLimitPoint (S : Set X) (ls : X) : Prop :=
  ∀ G : Set X, nbhd X τ G ls → ∃ s ∈ S, s ∈ G

def isClosure (S : Set X) (closureS : Set X) : Prop :=
  closureS = S ∪ {s | isLimitPoint X τ S s}

theorem closure_contains_set (S : Set X) (closureS : Set X) (h : isClosure X τ S closureS) : S ⊆ closureS := by
  rw [subset_def]
  intro x hx
  rw [isClosure] at h
  rw [h]
  exact mem_union_left {s | isLimitPoint X τ S s} hx

theorem subset_imp_closure_subset (S T cS cT : Set X) (hS : isClosure X τ S cS) (hT : isClosure X τ T cT) : S ⊆ T → cS ⊆ cT := by
  intro S_sub_T
  rw [isClosure] at *
  rw [subset_def] at *
  intro x hx
  by_cases xS : (x ∈ S)
  · specialize S_sub_T x
    apply S_sub_T at xS
    have T_sub_cT : T ⊆ cT := by
      exact closure_contains_set X τ T cT hT
    rw [subset_def] at T_sub_cT
    specialize T_sub_cT x
    apply T_sub_cT at xS
    exact xS
  · have x_islimitpointS : x ∈ {s | isLimitPoint X τ S s} := by
      rw [hS] at hx
      rw [@mem_union] at hx
      cases' hx with inconsistent goal
      · trivial
      · exact goal
    have x_islimitpointT : x ∈ {t | isLimitPoint X τ T t} := by
      rw [@mem_setOf] at x_islimitpointS
      rw [@mem_setOf]
      rw [isLimitPoint] at *
      intro G hG
      specialize x_islimitpointS G
      apply x_islimitpointS at hG
      cases' hG with w hw
      cases' hw with memS memG
      specialize S_sub_T w
      apply S_sub_T at memS
      use w
    rw [hT]
    exact mem_union_right T x_islimitpointT

theorem set_closed_imp_eq_closure (S cS: Set X) (hS : isClosed X τ S) (hcS : isClosure X τ S cS) : S = cS := by
  apply Subset.antisymm
  · exact closure_contains_set X τ S cS hcS
  · rw [@subset_def]
    by_contra hx
    push_neg at hx
    rw [isClosed] at hS
    rw [isClosure] at hcS
    cases' hx with x r1
    cases' r1 with x_mem_cS x_nMem_S
    have x_lpt_S : isLimitPoint X τ S x := by
      rw [hcS] at x_mem_cS
      rw [@mem_union] at x_mem_cS
      cases' x_mem_cS with inconsistent goal
      · trivial
      · exact goal
    rw [← @mem_compl_iff] at x_nMem_S
    rw [isLimitPoint] at x_lpt_S
    specialize x_lpt_S Sᶜ
    have compS_nbhd : nbhd X τ Sᶜ x := by
      rw [nbhd]
      exact ⟨x_nMem_S, hS⟩
    apply x_lpt_S at compS_nbhd
    cases' compS_nbhd with w hw
    exact (and_not_self_iff (w ∈ S)).mp hw

theorem eq_closure_imp_set_closed (S cS : Set X) (hS : S = cS) (hcS : isClosure X τ S cS) : isClosed X τ S := by
  rw [isClosed]
  rw [isClosure] at hcS
  refine nbhd_imp_open_2 X τ Sᶜ ?_
  intro a ha
  by_contra contra
  push_neg at contra
  have nbhd_uncontain : ∀ G : Set X, nbhd X τ G a → ¬G ⊆ Sᶜ := by
    intro G hG
    exact fun a => contra G a hG
  have a_lmpt : isLimitPoint X τ S a := by
    rw [isLimitPoint]
    have h1 : ∀ G : Set X, ¬G ⊆ Sᶜ → ∃ s ∈ S, s ∈ G := by
      intro G hG
      rw [@not_subset] at hG
      cases' hG with w right
      cases' right with w_memG w_nMemG
      rw [@not_mem_compl_iff] at w_nMemG
      use w
    exact fun G a => h1 G (nbhd_uncontain G a)
  have a_memcS : a ∈ cS := by
    rw [hcS]
    exact mem_union_right S a_lmpt
  rw [← hS] at a_memcS
  exact ha a_memcS

-- continuity !!!!
