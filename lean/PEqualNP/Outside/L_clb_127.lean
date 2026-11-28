import Mathlib
import PEqualNP.Defs

-- Pasted from accepted upstream proofs (renamed): L_lib_586, L_meta_25689, and the lower-bound half of L_clb_120.


namespace PEqualNP.Outside.L_clb_127.X586

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def Adj (E : List (ℕ × ℕ)) (x y : ℕ) : Prop :=
  (x, y) ∈ E ∨ (y, x) ∈ E

private def Reach (E : List (ℕ × ℕ)) (x y : ℕ) : Prop :=
  Relation.ReflTransGen (Adj E) x y

private theorem reach_refl (E : List (ℕ × ℕ)) (x : ℕ) : Reach E x x :=
  Relation.ReflTransGen.refl

private theorem reach_trans {E : List (ℕ × ℕ)} {x y z : ℕ}
    (h1 : Reach E x y) (h2 : Reach E y z) : Reach E x z :=
  Relation.ReflTransGen.trans h1 h2

private theorem reach_symm {E : List (ℕ × ℕ)} {x y : ℕ} (h : Reach E x y) : Reach E y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih =>
    exact Relation.ReflTransGen.head (by
      rcases hab with h1 | h2
      · exact Or.inr h1
      · exact Or.inl h2) ih

private theorem reach_mono {E1 E2 : List (ℕ × ℕ)} (hsub : ∀ e, e ∈ E1 → e ∈ E2)
    {x y : ℕ} (h : Reach E1 x y) : Reach E2 x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih =>
    apply Relation.ReflTransGen.tail ih
    rcases hab with h1 | h2
    · exact Or.inl (hsub _ h1)
    · exact Or.inr (hsub _ h2)

private theorem reach_iff_of_mem_iff {E1 E2 : List (ℕ × ℕ)} (hiff : ∀ e, e ∈ E1 ↔ e ∈ E2)
    (x y : ℕ) : Reach E1 x y ↔ Reach E2 x y :=
  ⟨reach_mono (fun e he => (hiff e).mp he), reach_mono (fun e he => (hiff e).mpr he)⟩

private noncomputable def comp (V : Finset ℕ) (E : List (ℕ × ℕ)) (x : ℕ) : Finset ℕ := by
  classical
  exact V.filter (fun y => Reach E x y)

private noncomputable def cc (V : Finset ℕ) (E : List (ℕ × ℕ)) : ℕ := by
  classical
  exact (V.image (comp V E)).card

private theorem mem_comp_iff {V : Finset ℕ} {E : List (ℕ × ℕ)} {x y : ℕ} :
    y ∈ comp V E x ↔ y ∈ V ∧ Reach E x y := by
  classical
  simp [comp]

private theorem comp_eq_iff {V : Finset ℕ} {E : List (ℕ × ℕ)} {x y : ℕ}
    (_hx : x ∈ V) (hy : y ∈ V) : comp V E x = comp V E y ↔ Reach E x y := by
  constructor
  · intro heq
    have : y ∈ comp V E x := by rw [heq]; exact mem_comp_iff.mpr ⟨hy, reach_refl E y⟩
    exact (mem_comp_iff.mp this).2
  · intro hxy
    ext z
    simp only [mem_comp_iff]
    exact ⟨fun ⟨hz, hxz⟩ => ⟨hz, reach_trans (reach_symm hxy) hxz⟩,
      fun ⟨hz, hyz⟩ => ⟨hz, reach_trans hxy hyz⟩⟩

private theorem cc_eq_of_mem_iff {V : Finset ℕ} {E1 E2 : List (ℕ × ℕ)}
    (hiff : ∀ e, e ∈ E1 ↔ e ∈ E2) : cc V E1 = cc V E2 := by
  classical
  have hc : comp V E1 = comp V E2 := by
    funext x
    ext y
    simp only [mem_comp_iff, reach_iff_of_mem_iff hiff]
  simp only [cc, hc]

private theorem cc_nil (V : Finset ℕ) : cc V [] = V.card := by
  classical
  have hc : ∀ x ∈ V, comp V [] x = {x} := by
    intro x hx
    ext y
    simp only [mem_comp_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩
      cases h with
      | refl => rfl
      | tail _ hab => simp [Adj] at hab
    · rintro rfl
      exact ⟨hx, reach_refl [] y⟩
  have heq : V.image (comp V []) = V.image (fun x => ({x} : Finset ℕ)) := by
    ext C
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (hc x hx).symm⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, hc x hx⟩
  simp only [cc, heq]
  rw [Finset.card_image_of_injective]
  intro a b h
  exact Finset.singleton_injective h

private theorem reach_cons_iff {E : List (ℕ × ℕ)} {u v x y : ℕ} :
    Reach ((u, v) :: E) x y ↔
      Reach E x y ∨ (Reach E x u ∧ Reach E v y) ∨ (Reach E x v ∧ Reach E u y) := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl (reach_refl E x)
    | @tail b c _ hbc ih =>
      have hstep : Adj E b c ∨ (b = u ∧ c = v) ∨ (b = v ∧ c = u) := by
        rcases hbc with h1 | h2
        · simp only [List.mem_cons, Prod.mk.injEq] at h1
          rcases h1 with ⟨rfl, rfl⟩ | h1'
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          · exact Or.inl (Or.inl h1')
        · simp only [List.mem_cons, Prod.mk.injEq] at h2
          rcases h2 with ⟨rfl, rfl⟩ | h2'
          · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
          · exact Or.inl (Or.inr h2')
      rcases hstep with hadj | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (Relation.ReflTransGen.tail h1 hadj)
        · exact Or.inr (Or.inl ⟨h1, Relation.ReflTransGen.tail h2 hadj⟩)
        · exact Or.inr (Or.inr ⟨h1, Relation.ReflTransGen.tail h2 hadj⟩)
      · rcases ih with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
        · exact Or.inr (Or.inl ⟨h1, reach_refl E c⟩)
        · exact Or.inr (Or.inl ⟨h1, reach_refl E c⟩)
        · exact Or.inl h1
      · rcases ih with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
        · exact Or.inr (Or.inr ⟨h1, reach_refl E c⟩)
        · exact Or.inl h1
        · exact Or.inr (Or.inr ⟨h1, reach_refl E c⟩)
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact reach_mono (fun e he => List.mem_cons_of_mem _ he) h
    · exact reach_trans (reach_mono (fun e he => List.mem_cons_of_mem _ he) h1)
        (Relation.ReflTransGen.head (Or.inl (List.mem_cons_self ..))
          (reach_mono (fun e he => List.mem_cons_of_mem _ he) h2))
    · exact reach_trans (reach_mono (fun e he => List.mem_cons_of_mem _ he) h1)
        (Relation.ReflTransGen.head (Or.inr (List.mem_cons_self ..))
          (reach_mono (fun e he => List.mem_cons_of_mem _ he) h2))

private theorem cc_cons_bounds {V : Finset ℕ} {E : List (ℕ × ℕ)} {u v : ℕ}
    (hu : u ∈ V) (hv : v ∈ V) :
    cc V ((u, v) :: E) ≤ cc V E ∧ cc V E ≤ cc V ((u, v) :: E) + 1 := by
  classical
  by_cases huv : Reach E u v
  · have hiff : ∀ x y, Reach ((u, v) :: E) x y ↔ Reach E x y := by
      intro x y
      rw [reach_cons_iff]
      constructor
      · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact h
        · exact reach_trans (reach_trans h1 huv) h2
        · exact reach_trans (reach_trans h1 (reach_symm huv)) h2
      · exact Or.inl
    have heq : cc V ((u, v) :: E) = cc V E := by
      have hc : comp V ((u, v) :: E) = comp V E := by
        funext x; ext y; simp only [mem_comp_iff, hiff]
      simp only [cc, hc]
    omega
  · let S := V.image (comp V E)
    let S' := V.image (comp V ((u, v) :: E))
    let Cu := comp V E u
    let Cv := comp V E v
    have hCuS : Cu ∈ S := Finset.mem_image.mpr ⟨u, hu, rfl⟩
    have hCvS : Cv ∈ S := Finset.mem_image.mpr ⟨v, hv, rfl⟩
    have hne : Cu ≠ Cv := fun h => huv ((comp_eq_iff hu hv).mp h)
    have hcomp_merge : ∀ x ∈ V,
        (Reach E x u ∨ Reach E x v → comp V ((u, v) :: E) x = Cu ∪ Cv) ∧
        (¬ Reach E x u ∧ ¬ Reach E x v → comp V ((u, v) :: E) x = comp V E x) := by
      intro x hx
      constructor
      · intro hxu
        ext y
        simp only [mem_comp_iff, Finset.mem_union, Cu, Cv, reach_cons_iff]
        constructor
        · rintro ⟨hy, h | ⟨_, h2⟩ | ⟨_, h2⟩⟩
          · rcases hxu with h1 | h1
            · exact Or.inl ⟨hy, reach_trans (reach_symm h1) h⟩
            · exact Or.inr ⟨hy, reach_trans (reach_symm h1) h⟩
          · exact Or.inr ⟨hy, h2⟩
          · exact Or.inl ⟨hy, h2⟩
        · rintro (⟨hy, huy⟩ | ⟨hy, hvy⟩)
          · rcases hxu with h1 | h1
            · exact ⟨hy, Or.inl (reach_trans h1 huy)⟩
            · exact ⟨hy, Or.inr (Or.inr ⟨h1, huy⟩)⟩
          · rcases hxu with h1 | h1
            · exact ⟨hy, Or.inr (Or.inl ⟨h1, hvy⟩)⟩
            · exact ⟨hy, Or.inl (reach_trans h1 hvy)⟩
      · rintro ⟨hnu, hnv⟩
        ext y
        simp only [mem_comp_iff, reach_cons_iff]
        constructor
        · rintro ⟨hy, h | ⟨h1, _⟩ | ⟨h1, _⟩⟩
          · exact ⟨hy, h⟩
          · exact absurd h1 hnu
          · exact absurd h1 hnv
        · rintro ⟨hy, h⟩
          exact ⟨hy, Or.inl h⟩
    have hS'_eq : S' = insert (Cu ∪ Cv) ((S.erase Cu).erase Cv) := by
      ext C
      simp only [S', S, Finset.mem_insert, Finset.mem_erase, Finset.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        by_cases hxu : Reach E x u ∨ Reach E x v
        · exact Or.inl ((hcomp_merge x hx).1 hxu)
        · push Not at hxu
          refine Or.inr ⟨?_, ?_, x, hx, ((hcomp_merge x hx).2 hxu).symm⟩
          · rw [(hcomp_merge x hx).2 hxu]
            exact fun h => hxu.2 ((comp_eq_iff hx hv).mp h)
          · rw [(hcomp_merge x hx).2 hxu]
            exact fun h => hxu.1 ((comp_eq_iff hx hu).mp h)
      · rintro (rfl | ⟨hCv', hCu', x, hx, rfl⟩)
        · exact ⟨u, hu, (hcomp_merge u hu).1 (Or.inl (reach_refl E u))⟩
        · have hnu : ¬ Reach E x u := fun h => hCu' ((comp_eq_iff hx hu).mpr h)
          have hnv : ¬ Reach E x v := fun h => hCv' ((comp_eq_iff hx hv).mpr h)
          exact ⟨x, hx, (hcomp_merge x hx).2 ⟨hnu, hnv⟩⟩
    have hnotmem : Cu ∪ Cv ∉ (S.erase Cu).erase Cv := by
      intro hmem
      rcases Finset.mem_erase.mp hmem with ⟨h1, hmem2⟩
      rcases Finset.mem_erase.mp hmem2 with ⟨h2, hmem3⟩
      rcases Finset.mem_image.mp hmem3 with ⟨x, hx, heq⟩
      have huin : u ∈ comp V E x := by
        rw [heq]; exact Finset.mem_union_left _ (mem_comp_iff.mpr ⟨hu, reach_refl E u⟩)
      have hxu : Reach E x u := (mem_comp_iff.mp huin).2
      have hCx : comp V E x = Cu := (comp_eq_iff hx hu).mpr hxu
      rw [hCx] at heq
      exact h2 heq.symm
    have hcard : S'.card + 1 = S.card := by
      rw [hS'_eq, Finset.card_insert_of_notMem hnotmem]
      have hCv_in : Cv ∈ S.erase Cu := Finset.mem_erase.mpr ⟨hne.symm, hCvS⟩
      rw [Finset.card_erase_of_mem hCv_in, Finset.card_erase_of_mem hCuS]
      have hge2 : 2 ≤ S.card := by
        have hsub : ({Cu, Cv} : Finset (Finset ℕ)) ⊆ S := by
          intro c hc
          simp only [Finset.mem_insert, Finset.mem_singleton] at hc
          rcases hc with rfl | rfl
          · exact hCuS
          · exact hCvS
        have h2 : ({Cu, Cv} : Finset (Finset ℕ)).card = 2 := Finset.card_pair hne
        have := Finset.card_le_card hsub
        omega
      omega
    change S'.card ≤ S.card ∧ S.card ≤ S'.card + 1
    omega

private theorem card_le_edges_add_cc {V : Finset ℕ} {E : List (ℕ × ℕ)}
    (hE : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V) :
    V.card ≤ E.length + cc V E := by
  induction E with
  | nil => rw [List.length_nil, zero_add, cc_nil]
  | cons e E ih =>
    rcases e with ⟨u, v⟩
    have he : u ∈ V ∧ v ∈ V := hE (u, v) (List.mem_cons_self ..)
    have hrest : ∀ e' ∈ E, e'.1 ∈ V ∧ e'.2 ∈ V := fun e' he' => hE e' (List.mem_cons_of_mem _ he')
    have hih := ih hrest
    have hb := (cc_cons_bounds (E := E) he.1 he.2).2
    simp only [List.length_cons]
    omega

private noncomputable def beta1 (V : Finset ℕ) (E : List (ℕ × ℕ)) : ℕ :=
  E.length + cc V E - V.card

private theorem beta1_add_card {V : Finset ℕ} {E : List (ℕ × ℕ)}
    (hE : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V) :
    V.card + beta1 V E = E.length + cc V E := by
  have h := card_le_edges_add_cc hE
  dsimp only [beta1]
  omega

private theorem cc_connected {V : Finset ℕ} {E : List (ℕ × ℕ)} {out : ℕ}
    (hout : out ∈ V) (hconn : ∀ x ∈ V, Reach E out x) : cc V E = 1 := by
  classical
  have heq : V.image (comp V E) = {comp V E out} := by
    ext C
    simp only [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (comp_eq_iff hx hout).mpr (reach_symm (hconn x hx))
    · rintro rfl
      exact ⟨out, hout, rfl⟩
  simp only [cc, heq, Finset.card_singleton]

private theorem beta1_delete_edge {V : Finset ℕ} {E1 E2 : List (ℕ × ℕ)} {e : ℕ × ℕ}
    (he1 : e.1 ∈ V) (he2 : e.2 ∈ V) :
    beta1 V (E1 ++ E2) ≤ beta1 V (E1 ++ e :: E2) := by
  rcases e with ⟨u, v⟩
  dsimp only at he1 he2
  have hiff : ∀ x, x ∈ (u, v) :: (E1 ++ E2) ↔ x ∈ E1 ++ (u, v) :: E2 := by
    intro x
    simp only [List.mem_cons, List.mem_append]
    tauto
  have hcc : cc V (E1 ++ (u, v) :: E2) = cc V ((u, v) :: (E1 ++ E2)) :=
    (cc_eq_of_mem_iff hiff).symm
  have hb := (cc_cons_bounds (E := E1 ++ E2) he1 he2).2
  dsimp only [beta1]
  rw [hcc]
  simp only [List.length_append, List.length_cons]
  omega

private theorem beta1_sublist {V : Finset ℕ} {E' E : List (ℕ × ℕ)}
    (hsub : E'.Sublist E) (hE : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V) :
    beta1 V E' ≤ beta1 V E := by
  have hgen : ∀ (P Q R : List (ℕ × ℕ)), P.Sublist Q →
      (∀ e ∈ R ++ Q, e.1 ∈ V ∧ e.2 ∈ V) → beta1 V (R ++ P) ≤ beta1 V (R ++ Q) := by
    intro P Q R hpq
    induction hpq generalizing R with
    | slnil => intro _; exact le_rfl
    | @cons p q x _ ih =>
      intro hRQ
      have hx : x.1 ∈ V ∧ x.2 ∈ V := hRQ x (List.mem_append_right _ (List.mem_cons_self ..))
      have h1 : beta1 V (R ++ p) ≤ beta1 V (R ++ q) :=
        ih R (fun e he => hRQ e (by
          rcases List.mem_append.mp he with h1 | h2
          · exact List.mem_append_left _ h1
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)))
      have h2 : beta1 V (R ++ q) ≤ beta1 V (R ++ x :: q) :=
        beta1_delete_edge hx.1 hx.2
      exact h1.trans h2
    | @cons_cons p q x _ ih =>
      intro hRQ
      have heq1 : R ++ x :: p = (R ++ [x]) ++ p := by simp
      have heq2 : R ++ x :: q = (R ++ [x]) ++ q := by simp
      rw [heq1, heq2]
      exact ih (R ++ [x]) (fun e he => by
        rw [← heq2] at he; exact hRQ e he)
  simpa using hgen E' E [] hsub (by simpa using hE)

private theorem cc_erase_isolated {V : Finset ℕ} {E : List (ℕ × ℕ)} {v : ℕ}
    (hv : v ∈ V) (hiso : ∀ e ∈ E, e.1 ≠ v ∧ e.2 ≠ v) :
    cc V E = cc (V.erase v) E + 1 := by
  classical
  have hreach_v : ∀ y, Reach E v y ↔ y = v := by
    intro y
    constructor
    · intro h
      induction h with
      | refl => rfl
      | tail _ hab ih =>
        subst ih
        rcases hab with h1 | h2
        · exact absurd rfl (hiso _ h1).1
        · exact absurd rfl (hiso _ h2).2
    · rintro rfl; exact reach_refl E _
  have hcv : comp V E v = {v} := by
    ext y
    simp only [mem_comp_iff, Finset.mem_singleton, hreach_v]
    constructor
    · rintro ⟨_, rfl⟩; rfl
    · intro hy; subst hy; exact ⟨hv, rfl⟩
  have hcx : ∀ x ∈ V.erase v, comp V E x = comp (V.erase v) E x := by
    intro x hx
    have hxv : x ≠ v := (Finset.mem_erase.mp hx).1
    ext y
    simp only [mem_comp_iff, Finset.mem_erase]
    constructor
    · rintro ⟨hy, hxy⟩
      refine ⟨⟨fun hyv => hxv ?_, hy⟩, hxy⟩
      subst hyv
      exact (hreach_v x).mp (reach_symm hxy)
    · rintro ⟨⟨_, hy⟩, hxy⟩
      exact ⟨hy, hxy⟩
  have heq : V.image (comp V E) = insert ({v} : Finset ℕ) ((V.erase v).image (comp (V.erase v) E)) := by
    ext C
    simp only [Finset.mem_image, Finset.mem_insert]
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_cases hxv : x = v
      · subst hxv; exact Or.inl hcv
      · exact Or.inr ⟨x, Finset.mem_erase.mpr ⟨hxv, hx⟩, (hcx x (Finset.mem_erase.mpr ⟨hxv, hx⟩)).symm⟩
    · rintro (rfl | ⟨x, hx, rfl⟩)
      · exact ⟨v, hv, hcv⟩
      · exact ⟨x, Finset.mem_of_mem_erase hx, hcx x hx⟩
  have hnm : ({v} : Finset ℕ) ∉ (V.erase v).image (comp (V.erase v) E) := by
    intro hm
    rcases Finset.mem_image.mp hm with ⟨x, _, he⟩
    have hv_in : v ∈ comp (V.erase v) E x := by rw [he]; simp
    exact (Finset.mem_erase.mp (mem_comp_iff.mp hv_in).1).1 rfl
  simp only [cc, heq, Finset.card_insert_of_notMem hnm]

private theorem beta1_erase_isolated {V : Finset ℕ} {E : List (ℕ × ℕ)} {v : ℕ}
    (hv : v ∈ V) (hiso : ∀ e ∈ E, e.1 ≠ v ∧ e.2 ≠ v) :
    beta1 (V.erase v) E = beta1 V E := by
  dsimp only [beta1]
  rw [cc_erase_isolated hv hiso, Finset.card_erase_of_mem hv]
  have hpos : 1 ≤ V.card := Finset.card_pos.mpr ⟨v, hv⟩
  omega

private theorem beta1_restrict_isolated {R V : Finset ℕ} {E : List (ℕ × ℕ)}
    (hRV : R ⊆ V) (hER : ∀ e ∈ E, e.1 ∈ R ∧ e.2 ∈ R) :
    beta1 R E = beta1 V E := by
  have hgen : ∀ (D : Finset ℕ), Disjoint R D → beta1 R E = beta1 (R ∪ D) E := by
    intro D
    induction D using Finset.induction_on with
    | empty => intro _; simp
    | @insert v D hvD ih =>
      intro hdisj
      have hvR : v ∉ R := fun h => (Finset.disjoint_left.mp hdisj) h (Finset.mem_insert_self _ _)
      have hdisj' : Disjoint R D := Disjoint.mono_right (Finset.subset_insert _ _) hdisj
      have hiso : ∀ e ∈ E, e.1 ≠ v ∧ e.2 ≠ v := fun e he =>
        ⟨fun h => hvR (h ▸ (hER e he).1), fun h => hvR (h ▸ (hER e he).2)⟩
      have hvin : v ∈ R ∪ insert v D := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
      have her : (R ∪ insert v D).erase v = R ∪ D := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_insert]
        constructor
        · rintro ⟨hne, hR | rfl | hD⟩
          · exact Or.inl hR
          · exact absurd rfl hne
          · exact Or.inr hD
        · rintro (hR | hD)
          · exact ⟨fun h => hvR (h ▸ hR), Or.inl hR⟩
          · exact ⟨fun h => hvD (h ▸ hD), Or.inr (Or.inr hD)⟩
      rw [ih hdisj', ← her, beta1_erase_isolated hvin hiso]
  have hunion : R ∪ (V \ R) = V := Finset.union_sdiff_of_subset hRV
  rw [← hunion]
  exact hgen (V \ R) Finset.disjoint_sdiff

private theorem beta1_contract {V : Finset ℕ} {E1 E2 : List (ℕ × ℕ)} {a v : ℕ}
    (ha : a ∈ V) (hv : v ∈ V) (hav : a ≠ v) :
    let sub : ℕ → ℕ := fun x => if x = v then a else x
    beta1 (V.erase v) ((E1 ++ E2).map (fun e => (sub e.1, sub e.2))) =
      beta1 V (E1 ++ (a, v) :: E2) := by
  classical
  intro sub
  let E := E1 ++ (a, v) :: E2
  let E' := (E1 ++ E2).map (fun e => (sub e.1, sub e.2))
  let V' := V.erase v
  have hsub_mem : ∀ x ∈ V, sub x ∈ V' := by
    intro x hx
    dsimp only [sub, V']
    split_ifs with h
    · exact Finset.mem_erase.mpr ⟨hav, ha⟩
    · exact Finset.mem_erase.mpr ⟨h, hx⟩
  have hsub_self : ∀ x, x ≠ v → sub x = x := fun x hx => by simp [sub, hx]
  have hreach_sub : ∀ x, Reach E x (sub x) := by
    intro x
    dsimp only [sub]
    split_ifs with h
    · subst h
      exact Relation.ReflTransGen.single (Or.inr (List.mem_append_right _ (List.mem_cons_self ..)))
    · exact reach_refl E x
  have hreach_iff : ∀ x y, Reach E' (sub x) (sub y) ↔ Reach E x y := by
    intro x y
    constructor
    · intro h
      have h' : ∀ p q, Reach E' p q → Reach E p q := by
        intro p q hpq
        induction hpq with
        | refl => exact reach_refl E p
        | tail _ hab ih =>
          refine reach_trans ih ?_
          rcases hab with h1 | h2
          · rcases List.mem_map.mp h1 with ⟨⟨r, s⟩, hrs, heq⟩
            rcases Prod.mk.inj heq with ⟨hr, hs⟩
            rw [← hr, ← hs]
            have hrsE : (r, s) ∈ E := by
              rcases List.mem_append.mp hrs with h1' | h2'
              · exact List.mem_append_left _ h1'
              · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2')
            exact reach_trans (reach_symm (hreach_sub r))
              (reach_trans (Relation.ReflTransGen.single (Or.inl hrsE)) (hreach_sub s))
          · rcases List.mem_map.mp h2 with ⟨⟨r, s⟩, hrs, heq⟩
            rcases Prod.mk.inj heq with ⟨hr, hs⟩
            rw [← hr, ← hs]
            have hrsE : (r, s) ∈ E := by
              rcases List.mem_append.mp hrs with h1' | h2'
              · exact List.mem_append_left _ h1'
              · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2')
            exact reach_trans (reach_symm (hreach_sub s))
              (reach_trans (Relation.ReflTransGen.single (Or.inr hrsE)) (hreach_sub r))
      exact reach_trans (hreach_sub x) (reach_trans (h' _ _ h) (reach_symm (hreach_sub y)))
    · intro h
      induction h with
      | refl => exact reach_refl E' (sub x)
      | @tail p q _ hpq ih =>
        refine reach_trans ih ?_
        have hstep : ∀ r s, (r, s) ∈ E → Reach E' (sub r) (sub s) := by
          intro r s hrs
          rcases List.mem_append.mp hrs with h1 | h2
          · exact Relation.ReflTransGen.single (Or.inl (List.mem_map.mpr ⟨(r, s),
              List.mem_append_left _ h1, rfl⟩))
          · rcases List.mem_cons.mp h2 with heq | h2'
            · rcases Prod.mk.inj heq with ⟨hra, hsv⟩
              rw [hra, hsv]
              have h1' : sub a = a := hsub_self a hav
              have h2' : sub v = a := by simp [sub]
              rw [h1', h2']; exact reach_refl E' a
            · exact Relation.ReflTransGen.single (Or.inl (List.mem_map.mpr ⟨(r, s),
                List.mem_append_right _ h2', rfl⟩))
        rcases hpq with h1 | h2
        · exact hstep p q h1
        · exact reach_symm (hstep q p h2)
  have hcomp_erase : ∀ x ∈ V, (comp V E x).erase v = comp V' E' (sub x) := by
    intro x _
    ext y
    simp only [Finset.mem_erase, mem_comp_iff, V']
    constructor
    · rintro ⟨hyv, hyV, hxy⟩
      refine ⟨⟨hyv, hyV⟩, ?_⟩
      rw [← hsub_self y hyv]
      exact (hreach_iff x y).mpr hxy
    · rintro ⟨⟨hyv, hyV⟩, hxy⟩
      refine ⟨hyv, hyV, (hreach_iff x y).mp ?_⟩
      rwa [hsub_self y hyv]
  let S := V.image (comp V E)
  let S' := V'.image (comp V' E')
  have hS'_eq : S' = S.image (fun C => C.erase v) := by
    ext D
    simp only [S', S, Finset.mem_image]
    constructor
    · rintro ⟨y, hyV', rfl⟩
      have hyV : y ∈ V := Finset.mem_of_mem_erase hyV'
      have hyv : y ≠ v := (Finset.mem_erase.mp hyV').1
      refine ⟨comp V E y, ⟨y, hyV, rfl⟩, ?_⟩
      rw [hcomp_erase y hyV, hsub_self y hyv]
    · rintro ⟨C, ⟨x, hxV, rfl⟩, rfl⟩
      exact ⟨sub x, hsub_mem x hxV, (hcomp_erase x hxV).symm⟩
  have hinj : Set.InjOn (fun C : Finset ℕ => C.erase v) (S : Set (Finset ℕ)) := by
    intro C1 hC1 C2 hC2 heq
    rcases Finset.mem_image.mp hC1 with ⟨x1, hx1, rfl⟩
    rcases Finset.mem_image.mp hC2 with ⟨x2, hx2, rfl⟩
    have hsub1_in : sub x1 ∈ (comp V E x1).erase v := by
      rw [hcomp_erase x1 hx1]
      exact mem_comp_iff.mpr ⟨hsub_mem x1 hx1, reach_refl E' (sub x1)⟩
    dsimp only at heq
    rw [heq, hcomp_erase x2 hx2] at hsub1_in
    have h21 : Reach E x2 x1 := (hreach_iff x2 x1).mp (mem_comp_iff.mp hsub1_in).2
    exact (comp_eq_iff hx1 hx2).mpr (reach_symm h21)
  have hcc_eq : cc V' E' = cc V E := by
    change S'.card = S.card
    rw [hS'_eq, Finset.card_image_of_injOn hinj]
  have hlen : E'.length + 1 = E.length := by
    dsimp only [E', E]
    simp only [List.length_map, List.length_append, List.length_cons]
    omega
  have hVcard : V'.card + 1 = V.card := by
    dsimp only [V']
    rw [Finset.card_erase_of_mem hv]
    have := Finset.card_pos.mpr ⟨v, hv⟩
    omega
  change E'.length + cc V' E' - V'.card = E.length + cc V E - V.card
  rw [hcc_eq]
  omega

private theorem foldl_wires_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
    acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

private theorem foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ)
    (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) acc).getD i false =
    acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (acc ++ [g.op.eval (g.inputs.map fun j => acc.getD j false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hi']
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem foldl_wires_getD_gate (gs : List Gate) (acc : List Bool) (t : ℕ)
    (ht : t < gs.length) :
    let final := gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) acc
    final.getD (acc.length + t) false =
      gs[t].op.eval (gs[t].inputs.map fun j => if j < acc.length + t then final.getD j false else false) := by
  induction gs generalizing acc t with
  | nil => simp at ht
  | cons g gs ih =>
    dsimp only
    cases t with
    | zero =>
      simp only [List.foldl_cons, add_zero, List.getElem_cons_zero]
      let step := acc ++ [g.op.eval (g.inputs.map fun j => acc.getD j false)]
      have hlen : acc.length < step.length := by
        dsimp only [step]; simp only [List.length_append, List.length_singleton]; omega
      rw [foldl_wires_getD_lt gs step acc.length hlen]
      have hstep_at : step.getD acc.length false =
          g.op.eval (g.inputs.map fun j => acc.getD j false) := by
        simp [step, List.getD_eq_getElem?_getD]
      rw [hstep_at]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < acc.length
      · simp only [hj, ↓reduceIte]
        have hj' : j < step.length := by omega
        rw [foldl_wires_getD_lt gs step j hj']
        simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
      · have hnone : acc[j]? = none := List.getElem?_eq_none (by omega)
        simp only [hj, ↓reduceIte, List.getD_eq_getElem?_getD, hnone]
        rfl
    | succ t =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      let step := acc ++ [g.op.eval (g.inputs.map fun j => acc.getD j false)]
      have ht' : t < gs.length := by simp at ht; omega
      have hlen : step.length = acc.length + 1 := by
        dsimp only [step]; simp only [List.length_append, List.length_singleton]
      have heq : acc.length + (t + 1) = step.length + t := by omega
      rw [heq]
      exact ih step t ht'

private theorem circuit_wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_length C.gates x

private theorem circuit_wires_getD_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  foldl_wires_getD_lt C.gates x i hi

private theorem circuit_wires_getD_gate (C : Circuit) (x : List Bool) (t : ℕ) (ht : t < C.gates.length) :
    (C.wires x).getD (x.length + t) false =
      C.gates[t].op.eval
        (C.gates[t].inputs.map fun j => if j < x.length + t then (C.wires x).getD j false else false) :=
  foldl_wires_getD_gate C.gates x t ht

private inductive NodeOp (k : ℕ)
  | inp (j : Fin k)
  | const (b : Bool)
  | copy (a : ℕ)
  | neg (a : ℕ)
  | bin (isAnd : Bool) (a b : ℕ)

private def nodeChildren {k : ℕ} : NodeOp k → List ℕ
  | NodeOp.inp _ => []
  | NodeOp.const _ => []
  | NodeOp.copy a => [a]
  | NodeOp.neg a => [a]
  | NodeOp.bin _ a b => [a, b]

private def mapNodeOp {k : ℕ} (f : ℕ → ℕ) : NodeOp k → NodeOp k
  | NodeOp.inp j => NodeOp.inp j
  | NodeOp.const b => NodeOp.const b
  | NodeOp.copy a => NodeOp.copy (f a)
  | NodeOp.neg a => NodeOp.neg (f a)
  | NodeOp.bin isAnd a b => NodeOp.bin isAnd (f a) (f b)

private def isNegOp {k : ℕ} : NodeOp k → Bool
  | NodeOp.neg _ => true
  | _ => false

private def isBinOp {k : ℕ} : NodeOp k → Bool
  | NodeOp.bin _ _ _ => true
  | _ => false

private def isInpOp {k : ℕ} : NodeOp k → Bool
  | NodeOp.inp _ => true
  | _ => false

private def isConstOp {k : ℕ} : NodeOp k → Bool
  | NodeOp.const _ => true
  | _ => false

private def isCopyOp {k : ℕ} : NodeOp k → Bool
  | NodeOp.copy _ => true
  | _ => false

private def evalOp {k : ℕ} (val : ℕ → Bool) (y : Fin k → Bool) : NodeOp k → Bool
  | NodeOp.inp j => y j
  | NodeOp.const b => b
  | NodeOp.copy a => val a
  | NodeOp.neg a => !(val a)
  | NodeOp.bin true a b => val a && val b
  | NodeOp.bin false a b => val a || val b

private theorem evalOp_congr {k : ℕ} {val1 val2 : ℕ → Bool} {y : Fin k → Bool} {o : NodeOp k}
    (h : ∀ a ∈ nodeChildren o, val1 a = val2 a) :
    evalOp val1 y o = evalOp val2 y o := by
  cases o with
  | inp _ => rfl
  | const _ => rfl
  | copy a => exact h a (by simp [nodeChildren])
  | neg a => simp only [evalOp, h a (by simp [nodeChildren])]
  | bin isAnd a b =>
    have ha := h a (by simp [nodeChildren])
    have hb := h b (by simp [nodeChildren])
    cases isAnd <;> simp only [evalOp, ha, hb]

private theorem evalOp_mapNodeOp {k : ℕ} {val1 val2 : ℕ → Bool} {y : Fin k → Bool}
    {f : ℕ → ℕ} {o : NodeOp k} (h : ∀ a ∈ nodeChildren o, val1 (f a) = val2 a) :
    evalOp val1 y (mapNodeOp f o) = evalOp val2 y o := by
  cases o with
  | inp _ => rfl
  | const _ => rfl
  | copy a => exact h a (by simp [nodeChildren])
  | neg a => simp only [mapNodeOp, evalOp, h a (by simp [nodeChildren])]
  | bin isAnd a b =>
    have ha := h a (by simp [nodeChildren])
    have hb := h b (by simp [nodeChildren])
    cases isAnd <;> simp only [mapNodeOp, evalOp, ha, hb]

private def evalFuel {k : ℕ} (op : ℕ → NodeOp k) (y : Fin k → Bool) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, v => evalOp (evalFuel op y fuel) y (op v)

private structure ValidDag (k : ℕ) where
  V : Finset ℕ
  op : ℕ → NodeOp k
  out : ℕ
  hout : out ∈ V
  hchild : ∀ v ∈ V, ∀ a ∈ nodeChildren (op v), a ∈ V ∧ a < v
  hinp_inj : ∀ v1 ∈ V, ∀ v2 ∈ V, ∀ j : Fin k,
    op v1 = NodeOp.inp j → op v2 = NodeOp.inp j → v1 = v2

private def evalDag {k : ℕ} (D : ValidDag k) (y : Fin k → Bool) (v : ℕ) : Bool :=
  evalFuel D.op y (v + 1) v

private theorem evalFuel_eq_of_ge {k : ℕ} (D : ValidDag k) (y : Fin k → Bool) :
    ∀ (v : ℕ), v ∈ D.V → ∀ (f : ℕ), v + 1 ≤ f → evalFuel D.op y f v = evalDag D y v := by
  intro v
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    intro hv f hf
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    dsimp only [evalDag, evalFuel]
    refine evalOp_congr (fun a ha => ?_)
    have hch := D.hchild v hv a ha
    rw [ih a hch.2 hch.1 f' (by omega), ih a hch.2 hch.1 v (by omega)]

private theorem evalDag_unfold {k : ℕ} (D : ValidDag k) (y : Fin k → Bool) {v : ℕ} (hv : v ∈ D.V) :
    evalDag D y v = evalOp (evalDag D y) y (D.op v) := by
  dsimp only [evalDag, evalFuel]
  refine evalOp_congr (fun a ha => ?_)
  have hch := D.hchild v hv a ha
  exact evalFuel_eq_of_ge D y a hch.1 v (by omega)

private def dagEdges {k : ℕ} (V : Finset ℕ) (op : ℕ → NodeOp k) : List (ℕ × ℕ) :=
  (V.sort (· ≤ ·)).flatMap (fun v => (nodeChildren (op v)).map (fun a => (a, v)))

private theorem dagEdges_allIn {k : ℕ} (D : ValidDag k) :
    ∀ e ∈ dagEdges D.V D.op, e.1 ∈ D.V ∧ e.2 ∈ D.V := by
  intro e he
  rcases List.mem_flatMap.mp he with ⟨v, hv, hev⟩
  have hvV : v ∈ D.V := (Finset.mem_sort (· ≤ ·)).mp hv
  rcases List.mem_map.mp hev with ⟨a, ha, rfl⟩
  exact ⟨(D.hchild v hvV a ha).1, hvV⟩

private theorem dagEdges_length {k : ℕ} (V : Finset ℕ) (op : ℕ → NodeOp k) :
    (dagEdges V op).length = ∑ v ∈ V, (nodeChildren (op v)).length := by
  dsimp only [dagEdges]
  rw [List.length_flatMap]
  have hmap : ((V.sort (· ≤ ·)).map (fun v => ((nodeChildren (op v)).map (fun a => (a, v))).length)) =
      (V.sort (· ≤ ·)).map (fun v => (nodeChildren (op v)).length) := by
    apply List.map_congr_left
    intro v _
    exact List.length_map _
  rw [hmap]
  rw [Finset.sum_eq_multiset_sum]
  have hcoe : ((V.sort (· ≤ ·) : List ℕ) : Multiset ℕ) = V.val := Finset.sort_eq (r := (· ≤ ·)) V
  rw [← hcoe, Multiset.map_coe, Multiset.sum_coe]

private def negCount {k : ℕ} (V : Finset ℕ) (op : ℕ → NodeOp k) : ℕ :=
  (V.filter (fun v => isNegOp (op v))).card

private def binCount {k : ℕ} (V : Finset ℕ) (op : ℕ → NodeOp k) : ℕ :=
  (V.filter (fun v => isBinOp (op v))).card

private def inpCount {k : ℕ} (V : Finset ℕ) (op : ℕ → NodeOp k) : ℕ :=
  (V.filter (fun v => isInpOp (op v))).card

private def constCount {k : ℕ} (V : Finset ℕ) (op : ℕ → NodeOp k) : ℕ :=
  (V.filter (fun v => isConstOp (op v))).card

private theorem dag_edge_vertex_identity {k : ℕ} (V : Finset ℕ) (op : ℕ → NodeOp k) :
    (dagEdges V op).length + inpCount V op + constCount V op = V.card + binCount V op := by
  rw [dagEdges_length]
  dsimp only [inpCount, constCount, binCount]
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
  have hcard : V.card = ∑ _ ∈ V, 1 := by simp
  rw [hcard, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  cases op v <;> simp [nodeChildren, isInpOp, isConstOp, isBinOp]

private theorem sublist_of_pairwise_lt {l1 l2 : List ℕ}
    (h1 : l1.Pairwise (· < ·)) (h2 : l2.Pairwise (· < ·))
    (hsub : ∀ x ∈ l1, x ∈ l2) : l1.Sublist l2 := by
  induction l2 generalizing l1 with
  | nil =>
    cases l1 with
    | nil => exact List.Sublist.slnil
    | cons a l1' =>
      exfalso
      exact List.not_mem_nil (hsub a (List.mem_cons_self ..))
  | cons b l2 ih =>
    cases l1 with
    | nil => exact List.nil_sublist _
    | cons a l1' =>
      have ha_in : a ∈ b :: l2 := hsub a (List.mem_cons_self ..)
      have hb_lt : ∀ y ∈ l2, b < y := (List.pairwise_cons.mp h2).1
      have h2' : l2.Pairwise (· < ·) := (List.pairwise_cons.mp h2).2
      have ha_lt : ∀ y ∈ l1', a < y := (List.pairwise_cons.mp h1).1
      have h1' : l1'.Pairwise (· < ·) := (List.pairwise_cons.mp h1).2
      rcases List.mem_cons.mp ha_in with rfl | ha2
      · refine List.Sublist.cons_cons a (ih h1' h2' ?_)
        intro x hx
        have hax : a < x := ha_lt x hx
        rcases List.mem_cons.mp (hsub x (List.mem_cons_of_mem _ hx)) with rfl | hx2
        · omega
        · exact hx2
      · refine List.Sublist.cons b (ih h1 h2' ?_)
        intro x hx
        have hba : b < a := hb_lt a ha2
        rcases List.mem_cons.mp (hsub x hx) with rfl | hx2
        · rcases List.mem_cons.mp hx with rfl | hx1'
          · omega
          · have := ha_lt x hx1'; omega
        · exact hx2

private theorem sort_sublist_of_subset {R V : Finset ℕ} (hRV : R ⊆ V) :
    (R.sort (· ≤ ·)).Sublist (V.sort (· ≤ ·)) := by
  have hp : ∀ S : Finset ℕ, (S.sort (· ≤ ·)).Pairwise (· < ·) := by
    intro S
    have hle := Finset.pairwise_sort S (· ≤ ·)
    have hnd := Finset.sort_nodup (r := (· ≤ ·)) S
    exact List.pairwise_iff_getElem.mpr (fun i j hi hj hij => by
      have h1 := List.pairwise_iff_getElem.mp hle i j hi hj hij
      have h2 := List.pairwise_iff_getElem.mp hnd i j hi hj hij
      omega)
  refine sublist_of_pairwise_lt (hp R) (hp V) ?_
  intro x hx
  exact (Finset.mem_sort (· ≤ ·)).mpr (hRV ((Finset.mem_sort (· ≤ ·)).mp hx))

private theorem sublist_flatMap {α β : Type} {l1 l2 : List α} (h : l1.Sublist l2) (f : α → List β) :
    (l1.flatMap f).Sublist (l2.flatMap f) := by
  induction h with
  | slnil => exact List.Sublist.slnil
  | cons a _ ih =>
    simp only [List.flatMap_cons]
    exact ih.trans (List.sublist_append_right _ _)
  | cons_cons a _ ih =>
    simp only [List.flatMap_cons]
    exact List.Sublist.append (List.Sublist.refl _) ih

private theorem flatMap_sublist_of_pointwise {α β : Type} (l : List α) (f g : α → List β)
    (h : ∀ x ∈ l, (f x).Sublist (g x)) : (l.flatMap f).Sublist (l.flatMap g) := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons a l ih =>
    simp only [List.flatMap_cons]
    exact List.Sublist.append (h a (List.mem_cons_self ..))
      (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

private def DirStep {k : ℕ} (D : ValidDag k) (x y : ℕ) : Prop :=
  y ∈ D.V ∧ x ∈ nodeChildren (D.op y)

private def DirReach {k : ℕ} (D : ValidDag k) (x y : ℕ) : Prop :=
  Relation.ReflTransGen (DirStep D) x y

private noncomputable def trimDag {k : ℕ} (D : ValidDag k) : ValidDag k := by
  classical
  let R := D.V.filter (fun x => DirReach D x D.out)
  refine ⟨R, D.op, D.out, ?_, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨D.hout, Relation.ReflTransGen.refl⟩
  · intro v hv a ha
    have hvV : v ∈ D.V := (Finset.mem_filter.mp hv).1
    have hvR : DirReach D v D.out := (Finset.mem_filter.mp hv).2
    have hch := D.hchild v hvV a ha
    refine ⟨Finset.mem_filter.mpr ⟨hch.1, Relation.ReflTransGen.head ⟨hvV, ha⟩ hvR⟩, hch.2⟩
  · intro v1 hv1 v2 hv2 j h1 h2
    exact D.hinp_inj v1 (Finset.mem_filter.mp hv1).1 v2 (Finset.mem_filter.mp hv2).1 j h1 h2

private theorem trimDag_connected {k : ℕ} (D : ValidDag k) :
    cc (trimDag D).V (dagEdges (trimDag D).V (trimDag D).op) = 1 := by
  classical
  refine cc_connected (trimDag D).hout ?_
  intro x hx
  have hdir : DirReach D x D.out := (Finset.mem_filter.mp hx).2
  have hback : ∀ u v, DirReach D u v → v ∈ (trimDag D).V →
      Reach (dagEdges (trimDag D).V (trimDag D).op) v u := by
    intro u v huv
    induction huv with
    | refl => intro _; exact reach_refl _ _
    | @tail b c _ hbc ih =>
      intro hcV
      have hbV : b ∈ (trimDag D).V := ((trimDag D).hchild c hcV b hbc.2).1
      have hedge : (b, c) ∈ dagEdges (trimDag D).V (trimDag D).op := by
        dsimp only [dagEdges]
        refine List.mem_flatMap.mpr ⟨c, (Finset.mem_sort (· ≤ ·)).mpr hcV, ?_⟩
        exact List.mem_map.mpr ⟨b, hbc.2, rfl⟩
      exact Relation.ReflTransGen.head (Or.inr hedge) (ih hbV)
  exact hback x D.out hdir (trimDag D).hout

private theorem trimDag_beta1 {k : ℕ} (D : ValidDag k) :
    beta1 (trimDag D).V (dagEdges (trimDag D).V (trimDag D).op) ≤
      beta1 D.V (dagEdges D.V D.op) := by
  classical
  have hRV : (trimDag D).V ⊆ D.V := Finset.filter_subset _ _
  have hsub : (dagEdges (trimDag D).V (trimDag D).op).Sublist (dagEdges D.V D.op) :=
    sublist_flatMap (sort_sublist_of_subset hRV) _
  have h1 := beta1_restrict_isolated hRV (dagEdges_allIn (trimDag D))
  have h2 := beta1_sublist hsub (dagEdges_allIn D)
  omega

private theorem trimDag_negCount {k : ℕ} (D : ValidDag k) :
    negCount (trimDag D).V (trimDag D).op ≤ negCount D.V D.op := by
  classical
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))

private def IsNormalForm {k : ℕ} (D : ValidDag k) : Prop :=
  (∀ x ∈ D.V, DirReach D x D.out) ∧
  (∀ v ∈ D.V, ¬ isConstOp (D.op v) ∧ ¬ isCopyOp (D.op v))

private theorem reduce_to_normal_form {k : ℕ} (D0 : ValidDag k)
    (hnc : ∃ y1 y2 : Fin k → Bool, evalDag D0 y1 D0.out ≠ evalDag D0 y2 D0.out) :
    ∃ D : ValidDag k,
      IsNormalForm D ∧
      beta1 D.V (dagEdges D.V D.op) ≤ beta1 D0.V (dagEdges D0.V D0.op) ∧
      negCount D.V D.op ≤ negCount D0.V D0.op ∧
      ∀ y : Fin k → Bool, evalDag D y D.out = evalDag D0 y D0.out := by
  classical
  have hmain : ∀ m : ℕ, ∀ D : ValidDag k,
      D.V.card + (dagEdges D.V D.op).length ≤ m →
      (∃ y1 y2 : Fin k → Bool, evalDag D y1 D.out ≠ evalDag D y2 D.out) →
      ∃ D' : ValidDag k,
        IsNormalForm D' ∧
        beta1 D'.V (dagEdges D'.V D'.op) ≤ beta1 D.V (dagEdges D.V D.op) ∧
        negCount D'.V D'.op ≤ negCount D.V D.op ∧
        ∀ y : Fin k → Bool, evalDag D' y D'.out = evalDag D y D.out := by
    intro m
    induction m with
    | zero =>
      intro D hm _
      have := Finset.card_pos.mpr ⟨D.out, D.hout⟩
      omega
    | succ m ih =>
      intro D hm hncD
      by_cases htrim : ∀ x ∈ D.V, DirReach D x D.out
      · by_cases halias : ∃ v ∈ D.V, ∃ a, D.op v = NodeOp.copy a
        · rcases halias with ⟨v, hvV, a, hopv⟩
          have ha := D.hchild v hvV a (by simp [hopv, nodeChildren])
          let sub : ℕ → ℕ := fun x => if x = v then a else x
          let V' := D.V.erase v
          let op' : ℕ → NodeOp k := fun u => mapNodeOp sub (D.op u)
          let out' := sub D.out
          have hsub_lt : ∀ u ∈ V', ∀ c ∈ nodeChildren (op' u), c ∈ V' ∧ c < u := by
            intro u huV' c hc
            have huV : u ∈ D.V := Finset.mem_of_mem_erase huV'
            have hch_map : nodeChildren (op' u) = (nodeChildren (D.op u)).map sub := by
              dsimp only [op']; cases D.op u <;> simp [mapNodeOp, nodeChildren]
            rw [hch_map] at hc
            rcases List.mem_map.mp hc with ⟨c0, hc0, rfl⟩
            have hc0_ok := D.hchild u huV c0 hc0
            dsimp only [sub]
            split_ifs with hcv
            · refine ⟨Finset.mem_erase.mpr ⟨by omega, ha.1⟩, by omega⟩
            · refine ⟨Finset.mem_erase.mpr ⟨hcv, hc0_ok.1⟩, hc0_ok.2⟩
          have hinj' : ∀ v1 ∈ V', ∀ v2 ∈ V', ∀ j : Fin k,
              op' v1 = NodeOp.inp j → op' v2 = NodeOp.inp j → v1 = v2 := by
            intro v1 hv1 v2 hv2 j h1 h2
            have h1' : D.op v1 = NodeOp.inp j := by
              dsimp only [op'] at h1; cases h : D.op v1 <;> simp [h, mapNodeOp] at h1 ⊢; exact h1
            have h2' : D.op v2 = NodeOp.inp j := by
              dsimp only [op'] at h2; cases h : D.op v2 <;> simp [h, mapNodeOp] at h2 ⊢; exact h2
            exact D.hinp_inj v1 (Finset.mem_of_mem_erase hv1) v2 (Finset.mem_of_mem_erase hv2) j h1' h2'
          have hout' : out' ∈ V' := by
            dsimp only [out', sub, V']
            split_ifs with h
            · exact Finset.mem_erase.mpr ⟨by omega, ha.1⟩
            · exact Finset.mem_erase.mpr ⟨h, D.hout⟩
          let D1 : ValidDag k := ⟨V', op', out', hout', hsub_lt, hinj'⟩
          have heval_all : ∀ y : Fin k → Bool, ∀ u ∈ D.V,
              evalDag D1 y (sub u) = evalDag D y u := by
            intro y u
            induction u using Nat.strong_induction_on with
            | ind u ihu =>
              intro huV
              by_cases huv : u = v
              · subst huv
                have hsubv : sub u = a := by simp [sub]
                have hsuba : sub a = a := by
                  dsimp only [sub]; split_ifs <;> omega
                rw [hsubv, evalDag_unfold D y huV, hopv]
                dsimp only [evalOp]
                rw [← ihu a ha.2 ha.1, hsuba]
              · have hsubu : sub u = u := by simp [sub, huv]
                have huV' : u ∈ V' := Finset.mem_erase.mpr ⟨huv, huV⟩
                rw [hsubu, evalDag_unfold D1 y huV', evalDag_unfold D y huV]
                change evalOp (evalDag D1 y) y (mapNodeOp sub (D.op u)) = evalOp (evalDag D y) y (D.op u)
                exact evalOp_mapNodeOp (fun c hc =>
                  ihu c (D.hchild u huV c hc).2 (D.hchild u huV c hc).1)
          have heval1 : ∀ y, evalDag D1 y D1.out = evalDag D y D.out :=
            fun y => heval_all y D.out D.hout
          have hbeta1 : beta1 D1.V (dagEdges D1.V D1.op) = beta1 D.V (dagEdges D.V D.op) := by
            have hv_sort : v ∈ D.V.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hvV
            rcases List.append_of_mem hv_sort with ⟨L1, L2, hL⟩
            have hLnd : (L1 ++ v :: L2).Nodup := by rw [← hL]; exact Finset.sort_nodup _ _
            have hv_not1 : v ∉ L1 := by
              intro h; exact (List.nodup_append.mp hLnd).2.2 v h v (List.mem_cons_self ..) rfl
            have hv_not2 : v ∉ L2 := (List.nodup_cons.mp (List.nodup_append.mp hLnd).2.1).1
            have hsort' : V'.sort (· ≤ ·) = L1 ++ L2 := by
              have hp1 : (V'.sort (· ≤ ·)).Pairwise (· < ·) := by
                have hle := Finset.pairwise_sort V' (· ≤ ·)
                have hnd := Finset.sort_nodup (r := (· ≤ ·)) V'
                exact List.pairwise_iff_getElem.mpr (fun i j hi hj hij => by
                  have h1 := List.pairwise_iff_getElem.mp hle i j hi hj hij
                  have h2 := List.pairwise_iff_getElem.mp hnd i j hi hj hij
                  omega)
              have hp2 : (L1 ++ L2).Pairwise (· < ·) := by
                have hfull : (D.V.sort (· ≤ ·)).Pairwise (· < ·) := by
                  have hle := Finset.pairwise_sort D.V (· ≤ ·)
                  have hnd := Finset.sort_nodup (r := (· ≤ ·)) D.V
                  exact List.pairwise_iff_getElem.mpr (fun i j hi hj hij => by
                    have h1 := List.pairwise_iff_getElem.mp hle i j hi hj hij
                    have h2 := List.pairwise_iff_getElem.mp hnd i j hi hj hij
                    omega)
                rw [hL] at hfull
                exact hfull.sublist (List.Sublist.append (List.Sublist.refl _) (List.sublist_cons_self _ _))
              have hmem_eq : ∀ x, x ∈ V'.sort (· ≤ ·) ↔ x ∈ L1 ++ L2 := by
                intro x
                rw [Finset.mem_sort, Finset.mem_erase, ← Finset.mem_sort (r := (· ≤ ·)), hL]
                simp only [List.mem_append, List.mem_cons]
                constructor
                · rintro ⟨hne, h1 | rfl | h2⟩
                  · exact Or.inl h1
                  · exact absurd rfl hne
                  · exact Or.inr h2
                · rintro (h1 | h2)
                  · exact ⟨fun h => hv_not1 (h ▸ h1), Or.inl h1⟩
                  · exact ⟨fun h => hv_not2 (h ▸ h2), Or.inr (Or.inr h2)⟩
              exact List.Sublist.antisymm
                (sublist_of_pairwise_lt hp1 hp2 (fun x hx => (hmem_eq x).mp hx))
                (sublist_of_pairwise_lt hp2 hp1 (fun x hx => (hmem_eq x).mpr hx))
            let fD : ℕ → List (ℕ × ℕ) := fun u => (nodeChildren (D.op u)).map (fun c => (c, u))
            let fD1 : ℕ → List (ℕ × ℕ) := fun u => (nodeChildren (op' u)).map (fun c => (c, u))
            have hE_eq : dagEdges D.V D.op = L1.flatMap fD ++ (a, v) :: L2.flatMap fD := by
              dsimp only [dagEdges, fD]
              rw [hL, List.flatMap_append, List.flatMap_cons, hopv]
              simp [nodeChildren]
            have hE1_eq : dagEdges D1.V D1.op =
                (L1.flatMap fD ++ L2.flatMap fD).map (fun e => (sub e.1, sub e.2)) := by
              dsimp only [dagEdges, D1]
              rw [hsort', List.flatMap_append, List.map_append]
              have hcongr : ∀ L : List ℕ, v ∉ L →
                  L.flatMap fD1 = (L.flatMap fD).map (fun e => (sub e.1, sub e.2)) := by
                intro L hnv
                rw [List.map_flatMap]
                apply List.flatMap_congr
                intro u hu
                have huv : u ≠ v := fun h => hnv (h ▸ hu)
                have hsubu : sub u = u := by simp [sub, huv]
                dsimp only [fD1, fD, op']
                cases D.op u <;> simp [mapNodeOp, nodeChildren, hsubu]
              exact congrArg₂ (· ++ ·) (hcongr L1 hv_not1) (hcongr L2 hv_not2)
            rw [hE_eq, hE1_eq]
            exact beta1_contract ha.1 hvV (by omega)
          have hneg1 : negCount D1.V D1.op ≤ negCount D.V D.op := by
            refine Finset.card_le_card ?_
            intro u hu
            rcases Finset.mem_filter.mp hu with ⟨huV', hneg⟩
            refine Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase huV', ?_⟩
            dsimp only [D1, op'] at hneg
            cases h : D.op u <;> simp [h, mapNodeOp, isNegOp] at hneg ⊢
          have hmeas : D1.V.card + (dagEdges D1.V D1.op).length ≤ m := by
            have hcard1 : D1.V.card + 1 = D.V.card := by
              dsimp only [D1, V']; rw [Finset.card_erase_of_mem hvV]
              have := Finset.card_pos.mpr ⟨v, hvV⟩; omega
            have hedge1 : (dagEdges D1.V D1.op).length ≤ (dagEdges D.V D.op).length := by
              rw [dagEdges_length, dagEdges_length]
              have hsub_V : D1.V ⊆ D.V := Finset.erase_subset _ _
              refine (Finset.sum_le_sum (fun u _ => ?_)).trans
                (Finset.sum_le_sum_of_subset hsub_V)
              dsimp only [D1, op']
              cases D.op u <;> simp [mapNodeOp, nodeChildren]
            omega
          have hnc1 : ∃ y1 y2, evalDag D1 y1 D1.out ≠ evalDag D1 y2 D1.out := by
            rcases hncD with ⟨y1, y2, hne⟩
            exact ⟨y1, y2, by rw [heval1 y1, heval1 y2]; exact hne⟩
          rcases ih D1 hmeas hnc1 with ⟨D', hnf, hb', hn', he'⟩
          exact ⟨D', hnf, hb'.trans (le_of_eq hbeta1), hn'.trans hneg1, fun y => (he' y).trans (heval1 y)⟩
        · have hno_alias : ∀ v ∈ D.V, ¬ isCopyOp (D.op v) := by
            intro v hvV hal
            cases hop : D.op v <;> simp [hop, isCopyOp] at hal
            exact halias ⟨v, hvV, _, hop⟩
          by_cases hdup : ∃ v ∈ D.V, ∃ isAnd a, D.op v = NodeOp.bin isAnd a a
          · rcases hdup with ⟨v, hvV, isAnd, a, hopv⟩
            let op' : ℕ → NodeOp k := fun u => if u = v then NodeOp.copy a else D.op u
            have hch' : ∀ u ∈ D.V, ∀ c ∈ nodeChildren (op' u), c ∈ D.V ∧ c < u := by
              intro u hu c hc
              dsimp only [op'] at hc
              split_ifs at hc with huv
              · subst huv
                have hc' : c = a := by simpa [nodeChildren] using hc
                subst hc'
                exact D.hchild u hu c (by simp [hopv, nodeChildren])
              · exact D.hchild u hu c hc
            have hinj' : ∀ v1 ∈ D.V, ∀ v2 ∈ D.V, ∀ j : Fin k,
                op' v1 = NodeOp.inp j → op' v2 = NodeOp.inp j → v1 = v2 := by
              intro v1 hv1 v2 hv2 j h1 h2
              dsimp only [op'] at h1 h2
              by_cases h1v : v1 = v
              · simp only [h1v, ↓reduceIte] at h1; cases h1
              · by_cases h2v : v2 = v
                · simp only [h2v, ↓reduceIte] at h2; cases h2
                · simp only [h1v, h2v, ↓reduceIte] at h1 h2
                  exact D.hinp_inj v1 hv1 v2 hv2 j h1 h2
            let D1 : ValidDag k := ⟨D.V, op', D.out, D.hout, hch', hinj'⟩
            have heval_all : ∀ y u, u ∈ D.V → evalDag D1 y u = evalDag D y u := by
              intro y u
              induction u using Nat.strong_induction_on with
              | ind u ihu =>
                intro huV
                rw [evalDag_unfold D1 y huV, evalDag_unfold D y huV]
                change evalOp (evalDag D1 y) y (op' u) = evalOp (evalDag D y) y (D.op u)
                dsimp only [op']
                split_ifs with huv
                · subst huv
                  have ha := D.hchild u huV a (by simp [hopv, nodeChildren])
                  rw [hopv]
                  simp only [evalOp, ihu a ha.2 ha.1]
                  cases isAnd <;> simp
                · exact evalOp_congr (fun c hc =>
                    ihu c (D.hchild u huV c hc).2 (D.hchild u huV c hc).1)
            have hsubE : (dagEdges D1.V D1.op).Sublist (dagEdges D.V D.op) := by
              dsimp only [dagEdges, D1]
              apply flatMap_sublist_of_pointwise
              intro u _
              dsimp only [op']
              split_ifs with huv
              · subst huv; rw [hopv]; simp [nodeChildren]
              · exact List.Sublist.refl _
            have hbeta1 : beta1 D1.V (dagEdges D1.V D1.op) ≤ beta1 D.V (dagEdges D.V D.op) :=
              beta1_sublist hsubE (dagEdges_allIn D)
            have hneg1 : negCount D1.V D1.op ≤ negCount D.V D.op := by
              refine Finset.card_le_card ?_
              intro u hu
              rcases Finset.mem_filter.mp hu with ⟨huV, hn⟩
              refine Finset.mem_filter.mpr ⟨huV, ?_⟩
              dsimp only [D1, op'] at hn
              split_ifs at hn with huv
              · simp [isNegOp] at hn
              · exact hn
            have hlen_lt : (dagEdges D1.V D1.op).length < (dagEdges D.V D.op).length := by
              rw [dagEdges_length, dagEdges_length]
              refine Finset.sum_lt_sum (fun u _ => ?_) ⟨v, hvV, ?_⟩
              · dsimp only [D1, op']; split_ifs with huv
                · subst huv; rw [hopv]; simp [nodeChildren]
                · exact le_rfl
              · dsimp only [D1, op']; simp [hopv, nodeChildren]
            have hmeas : D1.V.card + (dagEdges D1.V D1.op).length ≤ m := by
              have hVcard : D1.V.card = D.V.card := rfl
              omega
            have hnc1 : ∃ y1 y2, evalDag D1 y1 D1.out ≠ evalDag D1 y2 D1.out := by
              rcases hncD with ⟨y1, y2, hne⟩
              exact ⟨y1, y2, by rw [heval_all y1 D.out D.hout, heval_all y2 D.out D.hout]; exact hne⟩
            rcases ih D1 hmeas hnc1 with ⟨D', hnf, hb', hn', he'⟩
            exact ⟨D', hnf, hb'.trans hbeta1, hn'.trans hneg1,
              fun y => (he' y).trans (heval_all y D.out D.hout)⟩
          · by_cases hconst : ∃ c ∈ D.V, isConstOp (D.op c)
            · rcases hconst with ⟨c, hcV, hcop⟩
              cases hopc : D.op c with
              | const bval =>
                have hc_ne_out : c ≠ D.out := by
                  intro heq
                  subst heq
                  rcases hncD with ⟨y1, y2, hne⟩
                  rw [evalDag_unfold D y1 hcV, evalDag_unfold D y2 hcV, hopc] at hne
                  exact hne rfl
                have hparent : ∃ v ∈ D.V, c ∈ nodeChildren (D.op v) := by
                  have hrc : DirReach D c D.out := htrim c hcV
                  rcases Relation.ReflTransGen.cases_head hrc with rfl | ⟨w, hcw, _⟩
                  · exact absurd rfl hc_ne_out
                  · exact ⟨w, hcw.1, hcw.2⟩
                rcases hparent with ⟨v, hvV, hcv⟩
                have hred : ∃ newOp : NodeOp k,
                    (nodeChildren newOp).Sublist (nodeChildren (D.op v)) ∧
                    (nodeChildren newOp).length < (nodeChildren (D.op v)).length ∧
                    (isNegOp newOp = true → isNegOp (D.op v) = true) ∧
                    (∀ j, newOp ≠ NodeOp.inp j) ∧
                    ∀ y, evalOp (evalDag D y) y newOp = evalDag D y v := by
                  cases hopv : D.op v with
                  | inp j => simp [hopv, nodeChildren] at hcv
                  | const b => simp [hopv, nodeChildren] at hcv
                  | copy a => exact absurd (by simp [hopv, isCopyOp]) (hno_alias v hvV)
                  | neg a =>
                    have hac : c = a := by simpa [hopv, nodeChildren] using hcv
                    subst hac
                    refine ⟨NodeOp.const (!bval), by simp [nodeChildren], by simp [nodeChildren],
                      by simp [isNegOp], by intro j; simp, fun y => ?_⟩
                    rw [evalDag_unfold D y hvV, hopv]; simp only [evalOp, evalDag_unfold D y hcV, hopc]
                  | bin isAnd a b =>
                    have hab : c = a ∨ c = b := by simpa [hopv, nodeChildren] using hcv
                    rcases hab with rfl | rfl
                    · cases isAnd
                      · cases bval
                        · refine ⟨NodeOp.copy b, by simp [nodeChildren], by simp [nodeChildren],
                            by simp [isNegOp], by intro j; simp, fun y => ?_⟩
                          rw [evalDag_unfold D y hvV, hopv]; simp [evalOp, evalDag_unfold D y hcV, hopc]
                        · refine ⟨NodeOp.const true, by simp [nodeChildren], by simp [nodeChildren],
                            by simp [isNegOp], by intro j; simp, fun y => ?_⟩
                          rw [evalDag_unfold D y hvV, hopv]; simp [evalOp, evalDag_unfold D y hcV, hopc]
                      · cases bval
                        · refine ⟨NodeOp.const false, by simp [nodeChildren], by simp [nodeChildren],
                            by simp [isNegOp], by intro j; simp, fun y => ?_⟩
                          rw [evalDag_unfold D y hvV, hopv]; simp [evalOp, evalDag_unfold D y hcV, hopc]
                        · refine ⟨NodeOp.copy b, by simp [nodeChildren], by simp [nodeChildren],
                            by simp [isNegOp], by intro j; simp, fun y => ?_⟩
                          rw [evalDag_unfold D y hvV, hopv]; simp [evalOp, evalDag_unfold D y hcV, hopc]
                    · cases isAnd
                      · cases bval
                        · refine ⟨NodeOp.copy a, by simp [nodeChildren], by simp [nodeChildren],
                            by simp [isNegOp], by intro j; simp, fun y => ?_⟩
                          rw [evalDag_unfold D y hvV, hopv]; simp [evalOp, evalDag_unfold D y hcV, hopc]
                        · refine ⟨NodeOp.const true, by simp [nodeChildren], by simp [nodeChildren],
                            by simp [isNegOp], by intro j; simp, fun y => ?_⟩
                          rw [evalDag_unfold D y hvV, hopv]; simp [evalOp, evalDag_unfold D y hcV, hopc]
                      · cases bval
                        · refine ⟨NodeOp.const false, by simp [nodeChildren], by simp [nodeChildren],
                            by simp [isNegOp], by intro j; simp, fun y => ?_⟩
                          rw [evalDag_unfold D y hvV, hopv]; simp [evalOp, evalDag_unfold D y hcV, hopc]
                        · refine ⟨NodeOp.copy a, by simp [nodeChildren], by simp [nodeChildren],
                            by simp [isNegOp], by intro j; simp, fun y => ?_⟩
                          rw [evalDag_unfold D y hvV, hopv]; simp [evalOp, evalDag_unfold D y hcV, hopc]
                rcases hred with ⟨newOp, hsub_ch, hlen_ch, hneg_ch, hnoinp, heval_v⟩
                let op' : ℕ → NodeOp k := fun u => if u = v then newOp else D.op u
                have hch' : ∀ u ∈ D.V, ∀ a ∈ nodeChildren (op' u), a ∈ D.V ∧ a < u := by
                  intro u hu a ha
                  dsimp only [op'] at ha
                  split_ifs at ha with huv
                  · subst huv; exact D.hchild u hu a (hsub_ch.subset ha)
                  · exact D.hchild u hu a ha
                have hinj' : ∀ v1 ∈ D.V, ∀ v2 ∈ D.V, ∀ j : Fin k,
                    op' v1 = NodeOp.inp j → op' v2 = NodeOp.inp j → v1 = v2 := by
                  intro v1 hv1 v2 hv2 j h1 h2
                  dsimp only [op'] at h1 h2
                  by_cases h1v : v1 = v
                  · simp only [h1v, ↓reduceIte] at h1; exact absurd h1 (hnoinp j)
                  · by_cases h2v : v2 = v
                    · simp only [h2v, ↓reduceIte] at h2; exact absurd h2 (hnoinp j)
                    · simp only [h1v, h2v, ↓reduceIte] at h1 h2
                      exact D.hinp_inj v1 hv1 v2 hv2 j h1 h2
                let D1 : ValidDag k := ⟨D.V, op', D.out, D.hout, hch', hinj'⟩
                have heval_all : ∀ y u, u ∈ D.V → evalDag D1 y u = evalDag D y u := by
                  intro y u
                  induction u using Nat.strong_induction_on with
                  | ind u ihu =>
                    intro huV
                    rw [evalDag_unfold D1 y huV]
                    change evalOp (evalDag D1 y) y (op' u) = evalDag D y u
                    dsimp only [op']
                    split_ifs with huv
                    · subst huv
                      rw [← heval_v y]
                      exact evalOp_congr (fun a ha =>
                        ihu a (D.hchild u huV a (hsub_ch.subset ha)).2 (D.hchild u huV a (hsub_ch.subset ha)).1)
                    · rw [evalDag_unfold D y huV]
                      exact evalOp_congr (fun a ha =>
                        ihu a (D.hchild u huV a ha).2 (D.hchild u huV a ha).1)
                have hsubE : (dagEdges D1.V D1.op).Sublist (dagEdges D.V D.op) := by
                  dsimp only [dagEdges, D1]
                  apply flatMap_sublist_of_pointwise
                  intro u _
                  dsimp only [op']
                  split_ifs with huv
                  · subst huv; exact hsub_ch.map _
                  · exact List.Sublist.refl _
                have hbeta1 : beta1 D1.V (dagEdges D1.V D1.op) ≤ beta1 D.V (dagEdges D.V D.op) :=
                  beta1_sublist hsubE (dagEdges_allIn D)
                have hneg1 : negCount D1.V D1.op ≤ negCount D.V D.op := by
                  refine Finset.card_le_card ?_
                  intro u hu
                  rcases Finset.mem_filter.mp hu with ⟨huV, hn⟩
                  refine Finset.mem_filter.mpr ⟨huV, ?_⟩
                  dsimp only [D1, op'] at hn
                  split_ifs at hn with huv
                  · subst huv; exact hneg_ch hn
                  · exact hn
                have hlen_lt : (dagEdges D1.V D1.op).length < (dagEdges D.V D.op).length := by
                  rw [dagEdges_length, dagEdges_length]
                  refine Finset.sum_lt_sum (fun u _ => ?_) ⟨v, hvV, ?_⟩
                  · dsimp only [D1, op']; split_ifs with huv
                    · subst huv; exact le_of_lt hlen_ch
                    · exact le_rfl
                  · dsimp only [D1, op']; simp [hlen_ch]
                have hmeas : D1.V.card + (dagEdges D1.V D1.op).length ≤ m := by
                  have hVcard : D1.V.card = D.V.card := rfl
                  omega
                have hnc1 : ∃ y1 y2, evalDag D1 y1 D1.out ≠ evalDag D1 y2 D1.out := by
                  rcases hncD with ⟨y1, y2, hne⟩
                  exact ⟨y1, y2, by rw [heval_all y1 D.out D.hout, heval_all y2 D.out D.hout]; exact hne⟩
                rcases ih D1 hmeas hnc1 with ⟨D', hnf, hb', hn', he'⟩
                exact ⟨D', hnf, hb'.trans hbeta1, hn'.trans hneg1,
                  fun y => (he' y).trans (heval_all y D.out D.hout)⟩
              | inp _ => simp [hopc, isConstOp] at hcop
              | copy _ => simp [hopc, isConstOp] at hcop
              | neg _ => simp [hopc, isConstOp] at hcop
              | bin _ _ _ => simp [hopc, isConstOp] at hcop
            · push Not at hconst
              exact ⟨D, ⟨htrim, fun v hv => ⟨by intro h; exact absurd h (by simp [hconst v hv]),
                hno_alias v hv⟩⟩, le_rfl, le_rfl, fun _ => rfl⟩
      · let D1 := trimDag D
        have hlt_card : D1.V.card < D.V.card := by
          push Not at htrim
          rcases htrim with ⟨x, hxV, hxn⟩
          refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩)
          intro heq
          have hx1 : x ∈ D1.V := by rw [heq]; exact hxV
          exact hxn (Finset.mem_filter.mp hx1).2
        have hle_edges : (dagEdges D1.V D1.op).length ≤ (dagEdges D.V D.op).length :=
          (sublist_flatMap (sort_sublist_of_subset (Finset.filter_subset _ _)) _).length_le
        have hnc1 : ∃ y1 y2, evalDag D1 y1 D1.out ≠ evalDag D1 y2 D1.out := hncD
        rcases ih D1 (by omega) hnc1 with ⟨D', hnf, hb', hn', he'⟩
        exact ⟨D', hnf, hb'.trans (trimDag_beta1 D), hn'.trans (trimDag_negCount D),
          fun y => he' y⟩
  exact hmain (D0.V.card + (dagEdges D0.V D0.op).length) D0 le_rfl hnc

private theorem inv_eq_match (G : Circuit) :
    (G.gates.filter (fun g => @decide (g.op = GateOp.not) (Classical.propDecidable _))).length =
    (G.gates.filter (fun g => match g.op with | GateOp.not => true | _ => false)).length := by
  congr 1
  apply List.filter_congr
  intro g _
  cases g.op <;> simp

private theorem normal_form_to_circuit {k : ℕ} (D : ValidDag k) (hnf : IsNormalForm D) :
    ∃ G : Circuit,
      FanInTwo G ∧
      (G.gates.filter (fun g => @decide (g.op = GateOp.not) (Classical.propDecidable _))).length =
        negCount D.V D.op ∧
      G.size - (G.gates.filter (fun g => @decide (g.op = GateOp.not) (Classical.propDecidable _))).length =
        binCount D.V D.op ∧
      ∀ y : Fin k → Bool, G.eval (List.ofFn y) = evalDag D y D.out := by
  classical
  let Gset := D.V.filter (fun v => !(isInpOp (D.op v)))
  let gl := Gset.sort (· ≤ ·)
  have hgl_nodup : gl.Nodup := Finset.sort_nodup _ _
  have hgl_sorted : gl.Pairwise (· < ·) := by
    have hle : gl.Pairwise (· ≤ ·) := Finset.pairwise_sort Gset (· ≤ ·)
    exact List.pairwise_iff_getElem.mpr (fun i j hi hj hij => by
      have h1 := List.pairwise_iff_getElem.mp hle i j hi hj hij
      have h2 := List.pairwise_iff_getElem.mp hgl_nodup i j hi hj hij
      omega)
  have hgl_mem : ∀ v, v ∈ gl ↔ v ∈ Gset := fun v => Finset.mem_sort (· ≤ ·)
  let idx : ℕ → ℕ := fun v =>
    match D.op v with
    | NodeOp.inp j => j.val
    | _ => k + gl.idxOf v
  let mkGate : ℕ → Gate := fun v =>
    match D.op v with
    | NodeOp.neg a => ⟨GateOp.not, [idx a]⟩
    | NodeOp.bin true a b => ⟨GateOp.and, [idx a, idx b]⟩
    | NodeOp.bin false a b => ⟨GateOp.or, [idx a, idx b]⟩
    | _ => ⟨GateOp.or, []⟩
  let G : Circuit := ⟨gl.map mkGate, idx D.out⟩
  have hfan : FanInTwo G := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨v, _, rfl⟩
    dsimp only [mkGate]
    cases D.op v with
    | inp _ => simp
    | const _ => simp
    | copy _ => simp
    | neg _ => simp
    | bin isAnd _ _ => cases isAnd <;> simp
  have hidx_lt : ∀ v ∈ Gset, ∀ a ∈ nodeChildren (D.op v), idx a < k + gl.idxOf v := by
    intro v hvG a ha
    have hvV : v ∈ D.V := (Finset.mem_filter.mp hvG).1
    have hach := D.hchild v hvV a ha
    have hlt_gl : a ∈ gl → gl.idxOf a < gl.idxOf v := by
      intro haG
      have hvgl : v ∈ gl := (hgl_mem v).mpr hvG
      have hia : gl.idxOf a < gl.length := List.idxOf_lt_length_iff.mpr haG
      have hiv : gl.idxOf v < gl.length := List.idxOf_lt_length_iff.mpr hvgl
      have hgeta : gl[gl.idxOf a]'hia = a := List.getElem_idxOf hia
      have hgetv : gl[gl.idxOf v]'hiv = v := List.getElem_idxOf hiv
      by_contra hge
      rcases eq_or_lt_of_le (Nat.not_lt.mp hge) with heq | hgt
      · have hav : a = v := by rw [← hgeta, ← hgetv]; congr 1; exact heq.symm
        omega
      · have := List.pairwise_iff_getElem.mp hgl_sorted (gl.idxOf v) (gl.idxOf a) hiv hia hgt
        rw [hgetv, hgeta] at this; omega
    dsimp only [idx]
    cases hopa : D.op a with
    | inp j => dsimp only; have := j.isLt; omega
    | const _ => exact absurd (by simp [hopa, isConstOp]) (hnf.2 a hach.1).1
    | copy _ => exact absurd (by simp [hopa, isCopyOp]) (hnf.2 a hach.1).2
    | neg _ =>
      dsimp only
      have haG : a ∈ gl := (hgl_mem a).mpr (Finset.mem_filter.mpr ⟨hach.1, by simp [hopa, isInpOp]⟩)
      have := hlt_gl haG
      omega
    | bin _ _ _ =>
      dsimp only
      have haG : a ∈ gl := (hgl_mem a).mpr (Finset.mem_filter.mpr ⟨hach.1, by simp [hopa, isInpOp]⟩)
      have := hlt_gl haG
      omega
  have hinv_eq : (G.gates.filter (fun g => @decide (g.op = GateOp.not) (Classical.propDecidable _))).length =
      negCount D.V D.op := by
    rw [inv_eq_match]
    dsimp only [G]
    rw [List.filter_map, List.length_map]
    change (gl.filter (fun v => match (mkGate v).op with | GateOp.not => true | _ => false)).length = _
    have hperm : (gl.filter (fun v => match (mkGate v).op with | GateOp.not => true | _ => false)).Perm
        (D.V.filter (fun v => isNegOp (D.op v))).toList := by
      refine List.perm_ext_iff_of_nodup (hgl_nodup.filter _) (Finset.nodup_toList _) |>.mpr ?_
      intro v
      simp only [List.mem_filter, hgl_mem, Finset.mem_toList, Finset.mem_filter, Gset]
      constructor
      · rintro ⟨⟨hvV, _⟩, hnot⟩
        refine ⟨hvV, ?_⟩
        dsimp only [mkGate] at hnot
        cases h : D.op v with
        | neg _ => simp [isNegOp]
        | inp _ => simp [h] at hnot
        | const _ => simp [h] at hnot
        | copy _ => simp [h] at hnot
        | bin b _ _ => cases b <;> simp [h] at hnot
      · rintro ⟨hvV, hneg⟩
        cases h : D.op v with
        | neg _ => exact ⟨⟨hvV, by simp [isInpOp]⟩, by simp [mkGate, h]⟩
        | inp _ => simp [h, isNegOp] at hneg
        | const _ => simp [h, isNegOp] at hneg
        | copy _ => simp [h, isNegOp] at hneg
        | bin _ _ _ => simp [h, isNegOp] at hneg
    rw [hperm.length_eq, Finset.length_toList]
    rfl
  have hGsize : G.size = negCount D.V D.op + binCount D.V D.op := by
    dsimp only [Circuit.size, G]
    rw [List.length_map, Finset.length_sort]
    have hsplit : Gset = D.V.filter (fun v => isNegOp (D.op v)) ∪ D.V.filter (fun v => isBinOp (D.op v)) := by
      ext v
      simp only [Gset, Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hvV, hni⟩
        cases hop : D.op v with
        | inp _ => simp [hop, isInpOp] at hni
        | const _ => exact absurd (by simp [hop, isConstOp]) (hnf.2 v hvV).1
        | copy _ => exact absurd (by simp [hop, isCopyOp]) (hnf.2 v hvV).2
        | neg _ => exact Or.inl ⟨hvV, by simp [isNegOp]⟩
        | bin _ _ _ => exact Or.inr ⟨hvV, by simp [isBinOp]⟩
      · rintro (⟨hvV, hn⟩ | ⟨hvV, hb⟩)
        · cases hop : D.op v <;> simp [hop, isNegOp] at hn; exact ⟨hvV, by simp [isInpOp]⟩
        · cases hop : D.op v <;> simp [hop, isBinOp] at hb; exact ⟨hvV, by simp [isInpOp]⟩
    have hdisj : Disjoint (D.V.filter (fun v => isNegOp (D.op v))) (D.V.filter (fun v => isBinOp (D.op v))) := by
      rw [Finset.disjoint_left]
      intro v h1 h2
      have h1' := (Finset.mem_filter.mp h1).2
      have h2' := (Finset.mem_filter.mp h2).2
      cases hop : D.op v <;> simp [hop, isNegOp, isBinOp] at h1' h2'
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
    rfl
  have heval_G : ∀ y : Fin k → Bool, ∀ v ∈ D.V,
      (G.wires (List.ofFn y)).getD (idx v) false = evalDag D y v := by
    intro y v
    induction v using Nat.strong_induction_on with
    | ind v ih =>
      intro hvV
      rw [evalDag_unfold D y hvV]
      cases hopv : D.op v with
      | inp j =>
        have hidxv : idx v = j.val := by simp [idx, hopv]
        rw [hidxv, circuit_wires_getD_input G (List.ofFn y) j.val (by simp)]
        simp [List.getD_eq_getElem?_getD, evalOp]
      | const _ => exact absurd (by simp [hopv, isConstOp]) (hnf.2 v hvV).1
      | copy _ => exact absurd (by simp [hopv, isCopyOp]) (hnf.2 v hvV).2
      | neg a =>
        have hvG : v ∈ Gset := Finset.mem_filter.mpr ⟨hvV, by simp [hopv, isInpOp]⟩
        have hvgl : v ∈ gl := (hgl_mem v).mpr hvG
        have ht : gl.idxOf v < gl.length := List.idxOf_lt_length_iff.mpr hvgl
        have hidxv : idx v = (List.ofFn y).length + gl.idxOf v := by
          simp [idx, hopv]
        rw [hidxv, circuit_wires_getD_gate G (List.ofFn y) (gl.idxOf v) (by simp [G, ht])]
        have hget : G.gates[gl.idxOf v]'(by simp [G, ht]) = mkGate v := by
          dsimp only [G]
          rw [List.getElem_map, List.getElem_idxOf ht]
        rw [hget]
        dsimp only [mkGate]
        rw [hopv]
        have ha := D.hchild v hvV a (by simp [hopv, nodeChildren])
        have halt : idx a < (List.ofFn y).length + gl.idxOf v := by
          simpa using hidx_lt v hvG a (by simp [hopv, nodeChildren])
        simp only [List.map_cons, List.map_nil, halt, ↓reduceIte, GateOp.eval, List.headD_cons, evalOp]
        rw [ih a ha.2 ha.1]
      | bin isAnd a b =>
        have hvG : v ∈ Gset := Finset.mem_filter.mpr ⟨hvV, by simp [hopv, isInpOp]⟩
        have hvgl : v ∈ gl := (hgl_mem v).mpr hvG
        have ht : gl.idxOf v < gl.length := List.idxOf_lt_length_iff.mpr hvgl
        have hidxv : idx v = (List.ofFn y).length + gl.idxOf v := by
          simp [idx, hopv]
        rw [hidxv, circuit_wires_getD_gate G (List.ofFn y) (gl.idxOf v) (by simp [G, ht])]
        have hget : G.gates[gl.idxOf v]'(by simp [G, ht]) = mkGate v := by
          dsimp only [G]
          rw [List.getElem_map, List.getElem_idxOf ht]
        rw [hget]
        dsimp only [mkGate]
        rw [hopv]
        have ha := D.hchild v hvV a (by simp [hopv, nodeChildren])
        have hb := D.hchild v hvV b (by simp [hopv, nodeChildren])
        have halt : idx a < (List.ofFn y).length + gl.idxOf v := by
          simpa using hidx_lt v hvG a (by simp [hopv, nodeChildren])
        have hblt : idx b < (List.ofFn y).length + gl.idxOf v := by
          simpa using hidx_lt v hvG b (by simp [hopv, nodeChildren])
        cases isAnd
        · simp only [List.map_cons, List.map_nil, halt, hblt, ↓reduceIte, GateOp.eval,
            List.any_cons, List.any_nil, id_eq, Bool.or_false, evalOp]
          rw [ih a ha.2 ha.1, ih b hb.2 hb.1]
        · simp only [List.map_cons, List.map_nil, halt, hblt, ↓reduceIte, GateOp.eval,
            List.all_cons, List.all_nil, id_eq, Bool.and_true, evalOp]
          rw [ih a ha.2 ha.1, ih b hb.2 hb.1]
  refine ⟨G, hfan, hinv_eq, by omega, fun y => ?_⟩
  exact heval_G y D.out D.hout

private def gateToNodeOp {k : ℕ} (pos : ℕ) (g : Gate) : NodeOp k :=
  match g.op with
  | GateOp.not =>
    match g.inputs with
    | a :: _ => if a < pos then NodeOp.neg a else NodeOp.const true
    | [] => NodeOp.const true
  | GateOp.and =>
    match g.inputs with
    | [] => NodeOp.const true
    | [a] => if a < pos then NodeOp.copy a else NodeOp.const false
    | [a, b] => if a < pos ∧ b < pos then NodeOp.bin true a b else NodeOp.const false
    | _ => NodeOp.const false
  | GateOp.or =>
    match g.inputs with
    | [] => NodeOp.const false
    | [a] => if a < pos then NodeOp.copy a else NodeOp.const false
    | [a, b] =>
      if a < pos ∧ b < pos then NodeOp.bin false a b
      else if a < pos then NodeOp.copy a
      else if b < pos then NodeOp.copy b
      else NodeOp.const false
    | _ => NodeOp.const false
  | _ => NodeOp.const false

private theorem gateToNodeOp_ne_inp {k : ℕ} (pos : ℕ) (g : Gate) (j : Fin k) :
    gateToNodeOp (k := k) pos g ≠ NodeOp.inp j := by
  rcases g with ⟨gop, gins⟩
  cases gop with
  | not =>
    cases gins with
    | nil => simp [gateToNodeOp]
    | cons a _ => dsimp only [gateToNodeOp]; split_ifs <;> simp
  | and =>
    rcases gins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> dsimp only [gateToNodeOp]
    · simp
    · split_ifs <;> simp
    · split_ifs <;> simp
    · simp
  | or =>
    rcases gins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> dsimp only [gateToNodeOp]
    · simp
    · split_ifs <;> simp
    · split_ifs <;> simp
    · simp
  | mod _ => simp [gateToNodeOp]
  | maj => simp [gateToNodeOp]

private theorem gateToNodeOp_isNeg {k : ℕ} (pos : ℕ) (g : Gate)
    (h : isNegOp (gateToNodeOp (k := k) pos g) = true) : g.op = GateOp.not := by
  rcases g with ⟨gop, gins⟩
  cases gop with
  | not => rfl
  | and =>
    rcases gins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> dsimp only [gateToNodeOp] at h
    · simp [isNegOp] at h
    · split_ifs at h <;> simp [isNegOp] at h
    · split_ifs at h <;> simp [isNegOp] at h
    · simp [isNegOp] at h
  | or =>
    rcases gins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> dsimp only [gateToNodeOp] at h
    · simp [isNegOp] at h
    · split_ifs at h <;> simp [isNegOp] at h
    · split_ifs at h <;> simp [isNegOp] at h
    · simp [isNegOp] at h
  | mod _ => simp [gateToNodeOp, isNegOp] at h
  | maj => simp [gateToNodeOp, isNegOp] at h

private theorem gateToNodeOp_isBin {k : ℕ} (pos : ℕ) (g : Gate)
    (h : isBinOp (gateToNodeOp (k := k) pos g) = true) : g.op ≠ GateOp.not := by
  rcases g with ⟨gop, gins⟩
  intro heq
  subst heq
  cases gins with
  | nil => simp [gateToNodeOp, isBinOp] at h
  | cons a _ => dsimp only [gateToNodeOp] at h; split_ifs at h <;> simp [isBinOp] at h

private theorem gateToNodeOp_children {k : ℕ} (pos : ℕ) (g : Gate) :
    ∀ a ∈ nodeChildren (gateToNodeOp (k := k) pos g), a < pos := by
  rcases g with ⟨gop, gins⟩
  intro a ha
  cases gop with
  | not =>
    cases gins with
    | nil => simp [gateToNodeOp, nodeChildren] at ha
    | cons x xs =>
      dsimp only [gateToNodeOp] at ha
      split_ifs at ha with h
      · have hax : a = x := by simpa [nodeChildren] using ha
        omega
      · simp [nodeChildren] at ha
  | and =>
    rcases gins with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
    · simp [gateToNodeOp, nodeChildren] at ha
    · dsimp only [gateToNodeOp] at ha
      split_ifs at ha with h
      · have hax : a = x := by simpa [nodeChildren] using ha
        omega
      · simp [nodeChildren] at ha
    · dsimp only [gateToNodeOp] at ha
      split_ifs at ha with h
      · simp only [nodeChildren, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> [exact h.1; exact h.2]
      · simp [nodeChildren] at ha
    · simp [gateToNodeOp, nodeChildren] at ha
  | or =>
    rcases gins with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
    · simp [gateToNodeOp, nodeChildren] at ha
    · dsimp only [gateToNodeOp] at ha
      split_ifs at ha with h
      · have hax : a = x := by simpa [nodeChildren] using ha
        omega
      · simp [nodeChildren] at ha
    · dsimp only [gateToNodeOp] at ha
      split_ifs at ha with h1 h2 h3
      · simp only [nodeChildren, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> [exact h1.1; exact h1.2]
      · have hax : a = x := by simpa [nodeChildren] using ha
        omega
      · have hay : a = y := by simpa [nodeChildren] using ha
        omega
      · simp [nodeChildren] at ha
    · simp [gateToNodeOp, nodeChildren] at ha
  | mod _ => simp [gateToNodeOp, nodeChildren] at ha
  | maj => simp [gateToNodeOp, nodeChildren] at ha

private theorem gateToNodeOp_eval {k : ℕ} (pos : ℕ) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : g.inputs.length ≤ 2)
    (val : ℕ → Bool) (y : Fin k → Bool) :
    evalOp val y (gateToNodeOp (k := k) pos g) =
    g.op.eval (g.inputs.map (fun j => if j < pos then val j else false)) := by
  rcases g with ⟨gop, gins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · dsimp only [gateToNodeOp]
    rcases gins with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
    · simp [GateOp.eval, evalOp]
    · simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
        id_eq, Bool.and_true]
      split_ifs <;> rfl
    · simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
        id_eq, Bool.and_true]
      by_cases ha : a < pos <;> by_cases hb : b < pos <;> simp [ha, hb, evalOp]
    · simp at hlen
  · dsimp only [gateToNodeOp]
    rcases gins with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
    · simp [GateOp.eval, evalOp]
    · simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
        id_eq, Bool.or_false]
      split_ifs <;> rfl
    · simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
        id_eq, Bool.or_false]
      by_cases ha : a < pos <;> by_cases hb : b < pos <;> simp [ha, hb, evalOp]
    · simp at hlen
  · dsimp only [gateToNodeOp]
    rcases gins with _ | ⟨a, _⟩
    · simp [GateOp.eval, evalOp]
    · simp only [List.map_cons, GateOp.eval, List.headD_cons]
      split_ifs <;> rfl

private theorem solve_lib_586 (n k : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (wire : Fin k → Fin n) (fixed : Fin n → Bool) (hwinj : Function.Injective wire)
    (hnc : ∃ x y : Fin k → Bool,
      let plug := fun (z : Fin k → Bool) (i : Fin n) =>
        if i ∈ Finset.univ.image wire then decide (∃ j, wire j = i ∧ z j = true) else fixed i
      C.eval (List.ofFn (plug x)) ≠ C.eval (List.ofFn (plug y))) :
    let inv := fun (G : Circuit) =>
      (G.gates.filter (fun g => @decide (g.op = GateOp.not) (Classical.propDecidable _))).length
    let binary := fun (G : Circuit) => G.size - inv G
    let f := fun (x : Fin n → Bool) => C.eval (List.ofFn x)
    let e := ((Finset.univ : Finset (Fin n)).filter (fun i =>
      ∃ x : Fin n → Bool, f (Function.update x i false) ≠ f (Function.update x i true))).card
    let plug := fun (y : Fin k → Bool) (i : Fin n) =>
      if i ∈ Finset.univ.image wire then decide (∃ j, wire j = i ∧ y j = true) else fixed i
    ∃ D : Circuit, FanInTwo D ∧ binary D + e ≤ binary C + k ∧ inv D ≤ inv C ∧
      ∀ y : Fin k → Bool, D.eval (List.ofFn y) = f (plug y) := by
  classical
  dsimp only
  let inv := fun (G : Circuit) =>
    (G.gates.filter (fun g => @decide (g.op = GateOp.not) (Classical.propDecidable _))).length
  let binary := fun (G : Circuit) => G.size - inv G
  let f := fun (x : Fin n → Bool) => C.eval (List.ofFn x)
  let Ess := (Finset.univ : Finset (Fin n)).filter (fun i =>
    ∃ x : Fin n → Bool, f (Function.update x i false) ≠ f (Function.update x i true))
  let plug := fun (y : Fin k → Bool) (i : Fin n) =>
    if i ∈ Finset.univ.image wire then decide (∃ j, wire j = i ∧ y j = true) else fixed i
  have hout_lt : C.output < n + C.gates.length := by
    by_contra hge
    rcases hnc with ⟨x, y, hne⟩
    have hx : C.eval (List.ofFn (plug x)) = false := by
      dsimp only [Circuit.eval]
      have hlen : (C.wires (List.ofFn (plug x))).length = n + C.gates.length := by
        rw [circuit_wires_length, List.length_ofFn]
      have hnone : (C.wires (List.ofFn (plug x)))[C.output]? = none :=
        List.getElem?_eq_none (by omega)
      simp [List.getD_eq_getElem?_getD, hnone]
    have hy : C.eval (List.ofFn (plug y)) = false := by
      dsimp only [Circuit.eval]
      have hlen : (C.wires (List.ofFn (plug y))).length = n + C.gates.length := by
        rw [circuit_wires_length, List.length_ofFn]
      have hnone : (C.wires (List.ofFn (plug y)))[C.output]? = none :=
        List.getElem?_eq_none (by omega)
      simp [List.getD_eq_getElem?_getD, hnone]
    exact hne (by rw [hx, hy])
  let opRaw : ℕ → NodeOp n := fun v =>
    if hv : v < n then NodeOp.inp ⟨v, hv⟩
    else if hvt : v - n < C.gates.length then gateToNodeOp v (C.gates[v - n]'hvt)
    else NodeOp.const false
  have hch_raw : ∀ v ∈ Finset.range (n + C.gates.length), ∀ a ∈ nodeChildren (opRaw v),
      a ∈ Finset.range (n + C.gates.length) ∧ a < v := by
    intro v hv a ha
    have hvlt := Finset.mem_range.mp hv
    dsimp only [opRaw] at ha
    split_ifs at ha with h1 h2
    · simp [nodeChildren] at ha
    · have halt := gateToNodeOp_children v (C.gates[v - n]'h2) a ha
      exact ⟨Finset.mem_range.mpr (by omega), halt⟩
    · simp [nodeChildren] at ha
  have hinj_raw : ∀ v1 ∈ Finset.range (n + C.gates.length),
      ∀ v2 ∈ Finset.range (n + C.gates.length), ∀ j : Fin n,
      opRaw v1 = NodeOp.inp j → opRaw v2 = NodeOp.inp j → v1 = v2 := by
    intro v1 _ v2 _ j h1 h2
    have hlt_of : ∀ v, opRaw v = NodeOp.inp j → v = j.val := by
      intro v hv
      dsimp only [opRaw] at hv
      by_cases hvn : v < n
      · simp only [hvn, ↓reduceDIte] at hv
        exact congrArg Fin.val (NodeOp.inp.inj hv)
      · simp only [hvn, ↓reduceDIte] at hv
        by_cases hvt : v - n < C.gates.length
        · simp only [hvt, ↓reduceDIte] at hv
          exact absurd hv (gateToNodeOp_ne_inp v _ j)
        · simp only [hvt, ↓reduceDIte] at hv
          cases hv
    exact (hlt_of v1 h1).trans (hlt_of v2 h2).symm
  let Draw : ValidDag n := ⟨Finset.range (n + C.gates.length), opRaw, C.output,
    Finset.mem_range.mpr hout_lt, hch_raw, hinj_raw⟩
  have heval_raw : ∀ x : Fin n → Bool, ∀ v ∈ Draw.V,
      evalDag Draw x v = (C.wires (List.ofFn x)).getD v false := by
    intro x v
    induction v using Nat.strong_induction_on with
    | ind v ih =>
      intro hvV
      have hvlt := Finset.mem_range.mp hvV
      rw [evalDag_unfold Draw x hvV]
      change evalOp (evalDag Draw x) x (opRaw v) = _
      dsimp only [opRaw]
      split_ifs with h1 h2
      · rw [circuit_wires_getD_input C (List.ofFn x) v (by simp [h1])]
        simp [List.getD_eq_getElem?_getD, h1, evalOp]
      · have hveq : v = (List.ofFn x).length + (v - n) := by simp; omega
        have hg_mem : C.gates[v - n]'h2 ∈ C.gates := List.getElem_mem h2
        have hfg := hfan _ hg_mem
        have hget := circuit_wires_getD_gate C (List.ofFn x) (v - n) h2
        rw [← hveq] at hget
        rw [hget]
        have hcongr : evalOp (evalDag Draw x) x (gateToNodeOp (k := n) v (C.gates[v - n]'h2)) =
            evalOp (fun a => (C.wires (List.ofFn x)).getD a false) x
              (gateToNodeOp (k := n) v (C.gates[v - n]'h2)) := by
          refine evalOp_congr (fun a ha => ?_)
          have halt := gateToNodeOp_children (k := n) v (C.gates[v - n]'h2) a ha
          exact ih a halt (Finset.mem_range.mpr (by omega))
        rw [hcongr]
        exact gateToNodeOp_eval (k := n) v (C.gates[v - n]'h2) hfg.1 hfg.2
          (fun a => (C.wires (List.ofFn x)).getD a false) x
      · omega
  let Dtrim := trimDag Draw
  have hess_in : ∀ i ∈ Ess, i.val ∈ Dtrim.V := by
    intro i hi
    by_contra hnot
    rcases (Finset.mem_filter.mp hi).2 with ⟨x, hne⟩
    have hsame : ∀ v ∈ Dtrim.V,
        evalDag Dtrim (Function.update x i false) v = evalDag Dtrim (Function.update x i true) v := by
      intro v
      induction v using Nat.strong_induction_on with
      | ind v ih =>
        intro hv
        rw [evalDag_unfold Dtrim _ hv, evalDag_unfold Dtrim _ hv]
        cases hopv : Dtrim.op v with
        | inp j =>
          have hji : j ≠ i := by
            intro heq; subst heq
            have hvlt : v < n + C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hv).1
            have h1 := Draw.hinp_inj v (Finset.mem_range.mpr hvlt) j.val
              (Finset.mem_range.mpr (by omega)) j hopv (by simp [Draw, opRaw, j.isLt])
            rw [h1] at hv; exact hnot hv
          simp [evalOp, Function.update_of_ne hji]
        | const b => rfl
        | copy a =>
          have ha := Dtrim.hchild v hv a (by simp [hopv, nodeChildren])
          exact ih a ha.2 ha.1
        | neg a =>
          have ha := Dtrim.hchild v hv a (by simp [hopv, nodeChildren])
          simp only [evalOp, ih a ha.2 ha.1]
        | bin isAnd a b =>
          have ha := Dtrim.hchild v hv a (by simp [hopv, nodeChildren])
          have hb := Dtrim.hchild v hv b (by simp [hopv, nodeChildren])
          cases isAnd <;> simp only [evalOp, ih a ha.2 ha.1, ih b hb.2 hb.1]
    have h0 := hsame Dtrim.out Dtrim.hout
    change evalDag Draw (Function.update x i false) C.output =
      evalDag Draw (Function.update x i true) C.output at h0
    rw [heval_raw _ C.output Draw.hout, heval_raw _ C.output Draw.hout] at h0
    exact hne h0
  let opPlug : ℕ → NodeOp k := fun v =>
    match Dtrim.op v with
    | NodeOp.inp i =>
      if h : ∃ j : Fin k, wire j = i then NodeOp.inp (Classical.choose h)
      else NodeOp.const (fixed i)
    | NodeOp.const b => NodeOp.const b
    | NodeOp.copy a => NodeOp.copy a
    | NodeOp.neg a => NodeOp.neg a
    | NodeOp.bin isAnd a b => NodeOp.bin isAnd a b
  have hch_eq : ∀ v, nodeChildren (opPlug v) = nodeChildren (Dtrim.op v) := by
    intro v
    dsimp only [opPlug]
    cases Dtrim.op v with
    | inp i => dsimp only; split_ifs <;> rfl
    | const _ => rfl
    | copy _ => rfl
    | neg _ => rfl
    | bin _ _ _ => rfl
  have hinj_plug : ∀ v1 ∈ Dtrim.V, ∀ v2 ∈ Dtrim.V, ∀ j : Fin k,
      opPlug v1 = NodeOp.inp j → opPlug v2 = NodeOp.inp j → v1 = v2 := by
    intro v1 hv1 v2 hv2 j h1 h2
    have hof : ∀ v, opPlug v = NodeOp.inp j → Dtrim.op v = NodeOp.inp (wire j) := by
      intro v hv
      dsimp only [opPlug] at hv
      cases hopv : Dtrim.op v with
      | inp i =>
        rw [hopv] at hv; dsimp only at hv
        by_cases hex : ∃ j0 : Fin k, wire j0 = i
        · simp only [hex, ↓reduceDIte] at hv
          have ej : Classical.choose hex = j := NodeOp.inp.inj hv
          have hi : wire j = i := by rw [← ej]; exact Classical.choose_spec hex
          rw [hi]
        · simp only [hex, ↓reduceDIte] at hv; cases hv
      | const _ => rw [hopv] at hv; cases hv
      | copy _ => rw [hopv] at hv; cases hv
      | neg _ => rw [hopv] at hv; cases hv
      | bin _ _ _ => rw [hopv] at hv; cases hv
    exact Dtrim.hinp_inj v1 hv1 v2 hv2 (wire j) (hof v1 h1) (hof v2 h2)
  let Dplug : ValidDag k := ⟨Dtrim.V, opPlug, Dtrim.out, Dtrim.hout,
    fun v hv a ha => Dtrim.hchild v hv a (by rwa [← hch_eq v]), hinj_plug⟩
  have heval_plug : ∀ y : Fin k → Bool, ∀ v ∈ Dtrim.V,
      evalDag Dplug y v = evalDag Dtrim (plug y) v := by
    intro y v
    induction v using Nat.strong_induction_on with
    | ind v ih =>
      intro hv
      rw [evalDag_unfold Dplug y hv, evalDag_unfold Dtrim (plug y) hv]
      change evalOp (evalDag Dplug y) y (opPlug v) = evalOp (evalDag Dtrim (plug y)) (plug y) (Dtrim.op v)
      dsimp only [opPlug]
      cases hopv : Dtrim.op v with
      | inp i =>
        dsimp only [evalOp, plug]
        by_cases h1 : ∃ j : Fin k, wire j = i
        · have h2 : i ∈ Finset.univ.image wire := by
            rcases h1 with ⟨j, hj⟩; exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
          simp only [h1, h2, ↓reduceDIte, ↓reduceIte]
          have hj := Classical.choose_spec h1
          have hiff : (∃ j, wire j = i ∧ y j = true) ↔ y (Classical.choose h1) = true := by
            constructor
            · rintro ⟨j, hji, hyj⟩
              have : j = Classical.choose h1 := hwinj (hji.trans hj.symm)
              rwa [← this]
            · intro hy; exact ⟨Classical.choose h1, hj, hy⟩
          simp [hiff]
        · have h2 : i ∉ Finset.univ.image wire := by
            intro hm; rcases Finset.mem_image.mp hm with ⟨j, _, hj⟩; exact h1 ⟨j, hj⟩
          simp only [h1, h2, ↓reduceDIte, ↓reduceIte]
      | const b => rfl
      | copy a =>
        have ha := Dtrim.hchild v hv a (by simp [hopv, nodeChildren])
        exact ih a ha.2 ha.1
      | neg a =>
        have ha := Dtrim.hchild v hv a (by simp [hopv, nodeChildren])
        simp only [evalOp, ih a ha.2 ha.1]
      | bin isAnd a b =>
        have ha := Dtrim.hchild v hv a (by simp [hopv, nodeChildren])
        have hb := Dtrim.hchild v hv b (by simp [hopv, nodeChildren])
        cases isAnd <;> simp only [evalOp, ih a ha.2 ha.1, ih b hb.2 hb.1]
  have heval_plug_out : ∀ y : Fin k → Bool, evalDag Dplug y Dplug.out = f (plug y) := by
    intro y
    rw [heval_plug y Dtrim.out Dtrim.hout]
    change evalDag Draw (plug y) C.output = C.eval (List.ofFn (plug y))
    exact heval_raw (plug y) C.output Draw.hout
  have hnc_plug : ∃ y1 y2, evalDag Dplug y1 Dplug.out ≠ evalDag Dplug y2 Dplug.out := by
    rcases hnc with ⟨y1, y2, hne⟩
    exact ⟨y1, y2, by rw [heval_plug_out y1, heval_plug_out y2]; exact hne⟩
  have hedges_eq : dagEdges Dplug.V Dplug.op = dagEdges Dtrim.V Dtrim.op := by
    dsimp only [dagEdges, Dplug]
    apply List.flatMap_congr
    intro v _
    rw [hch_eq v]
  have hcc_plug : cc Dplug.V (dagEdges Dplug.V Dplug.op) = 1 := by
    rw [hedges_eq]; exact trimDag_connected Draw
  have hneg_plug_le : negCount Dplug.V Dplug.op ≤ inv C := by
    have h1 : negCount Dplug.V Dplug.op ≤ negCount Draw.V Draw.op := by
      refine Finset.card_le_card ?_
      intro v hv
      rcases Finset.mem_filter.mp hv with ⟨hvT, hneg⟩
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hvT).1, ?_⟩
      dsimp only [Dplug, opPlug] at hneg
      cases hop : Dtrim.op v with
      | neg _ => change isNegOp (Dtrim.op v) = true; rw [hop]; rfl
      | inp _ => rw [hop] at hneg; dsimp only at hneg; split_ifs at hneg <;> simp [isNegOp] at hneg
      | const _ => simp [hop, isNegOp] at hneg
      | copy _ => simp [hop, isNegOp] at hneg
      | bin _ _ _ => simp [hop, isNegOp] at hneg
    refine h1.trans ?_
    dsimp only [inv]
    rw [inv_eq_match]
    let S := (Finset.range C.gates.length).filter (fun t =>
      match (C.gates.getD t ⟨GateOp.or, []⟩).op with | GateOp.not => true | _ => false)
    have hsub : (Draw.V.filter (fun v => isNegOp (Draw.op v))) ⊆ S.image (fun t => n + t) := by
      intro v hv
      rcases Finset.mem_filter.mp hv with ⟨hvR, hneg⟩
      have hvlt := Finset.mem_range.mp hvR
      dsimp only [Draw, opRaw] at hneg
      split_ifs at hneg with h1 h2
      · simp [isNegOp] at hneg
      · refine Finset.mem_image.mpr ⟨v - n, ?_, by omega⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h2, ?_⟩
        have hgetD : C.gates.getD (v - n) ⟨GateOp.or, []⟩ = C.gates[v - n]'h2 := by
          simp [List.getD_eq_getElem?_getD, h2]
        rw [hgetD, gateToNodeOp_isNeg v _ hneg]
      · simp [isNegOp] at hneg
    have hScard : S.card = (C.gates.filter (fun g => match g.op with | GateOp.not => true | _ => false)).length := by
      clear hsub h1
      let P : Gate → Bool := fun g => match g.op with | GateOp.not => true | _ => false
      have hgen : ∀ (L : List Gate),
          ((Finset.range L.length).filter (fun t => P (L.getD t ⟨GateOp.or, []⟩) = true)).card =
          (L.filter P).length := by
        intro L
        induction L with
        | nil => simp
        | cons g L ih =>
          simp only [List.length_cons, List.filter_cons]
          have hr : Finset.range (L.length + 1) = insert 0 ((Finset.range L.length).image Nat.succ) := by
            ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_image]
            cases x with
            | zero => simp
            | succ x => simp
          rw [hr, Finset.filter_insert]
          have hflt_img : ((Finset.range L.length).image Nat.succ).filter
              (fun t => P ((g :: L).getD t ⟨GateOp.or, []⟩) = true) =
              ((Finset.range L.length).filter
                (fun t => P (L.getD t ⟨GateOp.or, []⟩) = true)).image Nat.succ := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_image]
            constructor
            · rintro ⟨⟨t, ht, rfl⟩, hp⟩
              exact ⟨t, ⟨ht, by simpa [List.getD_eq_getElem?_getD] using hp⟩, rfl⟩
            · rintro ⟨t, ⟨ht, hp⟩, rfl⟩
              exact ⟨⟨t, ht, rfl⟩, by simpa [List.getD_eq_getElem?_getD] using hp⟩
          have h0_eq : (g :: L).getD 0 ⟨GateOp.or, []⟩ = g := rfl
          rw [h0_eq, hflt_img]
          have h0nm : (0 : ℕ) ∉ ((Finset.range L.length).filter (fun t => P (L.getD t ⟨GateOp.or, []⟩) = true)).image Nat.succ := by
            simp
          cases hPg : P g
          · simp only [Bool.false_eq_true, ↓reduceIte, Finset.card_image_of_injective _ Nat.succ_injective, ih]
          · simp only [↓reduceIte, Finset.card_insert_of_notMem h0nm,
              Finset.card_image_of_injective _ Nat.succ_injective, List.length_cons, ih]
      convert hgen C.gates using 2
      ext t; simp [S, P]; intro _; cases (C.gates[t]?.getD ⟨GateOp.or, []⟩).op <;> simp
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (le_of_eq hScard))
  have hbin_plug_le : binCount Dplug.V Dplug.op ≤ binary C := by
    have h1 : binCount Dplug.V Dplug.op ≤ binCount Draw.V Draw.op := by
      refine Finset.card_le_card ?_
      intro v hv
      rcases Finset.mem_filter.mp hv with ⟨hvT, hbin⟩
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hvT).1, ?_⟩
      dsimp only [Dplug, opPlug] at hbin
      cases hop : Dtrim.op v with
      | bin _ _ _ => change isBinOp (Dtrim.op v) = true; rw [hop]; rfl
      | inp _ => rw [hop] at hbin; dsimp only at hbin; split_ifs at hbin <;> simp [isBinOp] at hbin
      | const _ => simp [hop, isBinOp] at hbin
      | copy _ => simp [hop, isBinOp] at hbin
      | neg _ => simp [hop, isBinOp] at hbin
    refine h1.trans ?_
    dsimp only [binary, inv, Circuit.size]
    rw [inv_eq_match]
    let S := (Finset.range C.gates.length).filter (fun t =>
      match (C.gates.getD t ⟨GateOp.or, []⟩).op with | GateOp.not => false | _ => true)
    have hsub : (Draw.V.filter (fun v => isBinOp (Draw.op v))) ⊆ S.image (fun t => n + t) := by
      intro v hv
      rcases Finset.mem_filter.mp hv with ⟨hvR, hbin⟩
      have hvlt := Finset.mem_range.mp hvR
      dsimp only [Draw, opRaw] at hbin
      split_ifs at hbin with h1 h2
      · simp [isBinOp] at hbin
      · refine Finset.mem_image.mpr ⟨v - n, ?_, by omega⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h2, ?_⟩
        have hgetD : C.gates.getD (v - n) ⟨GateOp.or, []⟩ = C.gates[v - n]'h2 := by
          simp [List.getD_eq_getElem?_getD, h2]
        rw [hgetD]
        have hne_not := gateToNodeOp_isBin v _ hbin
        cases hop : (C.gates[v - n]'h2).op with
        | not => exact absurd hop hne_not
        | and => rfl
        | or => rfl
        | mod _ => rfl
        | maj => rfl
      · simp [isBinOp] at hbin
    have hScard : S.card = C.gates.length -
        (C.gates.filter (fun g => match g.op with | GateOp.not => true | _ => false)).length := by
      clear hsub h1
      let P : Gate → Bool := fun g => match g.op with | GateOp.not => true | _ => false
      let Q : Gate → Bool := fun g => match g.op with | GateOp.not => false | _ => true
      have hPQ : ∀ g, Q g = !(P g) := fun ⟨gop, _⟩ => by cases gop <;> rfl
      have hgen : ∀ (L : List Gate),
          ((Finset.range L.length).filter (fun t => Q (L.getD t ⟨GateOp.or, []⟩) = true)).card +
          (L.filter P).length = L.length := by
        intro L
        induction L with
        | nil => simp
        | cons g L ih =>
          simp only [List.length_cons, List.filter_cons]
          have hr : Finset.range (L.length + 1) = insert 0 ((Finset.range L.length).image Nat.succ) := by
            ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_image]
            cases x with
            | zero => simp
            | succ x => simp
          rw [hr, Finset.filter_insert]
          have hflt_img : ((Finset.range L.length).image Nat.succ).filter
              (fun t => Q ((g :: L).getD t ⟨GateOp.or, []⟩) = true) =
              ((Finset.range L.length).filter
                (fun t => Q (L.getD t ⟨GateOp.or, []⟩) = true)).image Nat.succ := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_image]
            constructor
            · rintro ⟨⟨t, ht, rfl⟩, hp⟩
              exact ⟨t, ⟨ht, by simpa [List.getD_eq_getElem?_getD] using hp⟩, rfl⟩
            · rintro ⟨t, ⟨ht, hp⟩, rfl⟩
              exact ⟨⟨t, ht, rfl⟩, by simpa [List.getD_eq_getElem?_getD] using hp⟩
          have h0_eq : (g :: L).getD 0 ⟨GateOp.or, []⟩ = g := rfl
          rw [h0_eq, hflt_img, hPQ g]
          have h0nm : (0 : ℕ) ∉ ((Finset.range L.length).filter (fun t => Q (L.getD t ⟨GateOp.or, []⟩) = true)).image Nat.succ := by
            simp
          cases hPg : P g
          · simp only [Bool.false_eq_true, Bool.not_false, ↓reduceIte, Finset.card_insert_of_notMem h0nm,
              Finset.card_image_of_injective _ Nat.succ_injective]
            omega
          · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              Finset.card_image_of_injective _ Nat.succ_injective, List.length_cons]
            omega
      have hsum : S.card +
          (C.gates.filter P).length = C.gates.length := by
        convert hgen C.gates using 3
        ext t; simp [S, Q]; intro _; cases (C.gates[t]?.getD ⟨GateOp.or, []⟩).op <;> simp
      exact Nat.eq_sub_of_add_eq hsum
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (le_of_eq hScard))
  have hess_le_ic : Ess.card ≤ inpCount Dplug.V Dplug.op + constCount Dplug.V Dplug.op := by
    let U := Dplug.V.filter (fun v => isInpOp (Dplug.op v) ∨ isConstOp (Dplug.op v))
    have hUcard : U.card = inpCount Dplug.V Dplug.op + constCount Dplug.V Dplug.op := by
      have hsplit : U = Dplug.V.filter (fun v => isInpOp (Dplug.op v)) ∪
          Dplug.V.filter (fun v => isConstOp (Dplug.op v)) := by
        ext v; simp only [U, Finset.mem_filter, Finset.mem_union]; tauto
      have hdisj : Disjoint (Dplug.V.filter (fun v => isInpOp (Dplug.op v)))
          (Dplug.V.filter (fun v => isConstOp (Dplug.op v))) := by
        rw [Finset.disjoint_left]
        intro v h1 h2
        have h1' := (Finset.mem_filter.mp h1).2
        have h2' := (Finset.mem_filter.mp h2).2
        cases hop : Dplug.op v <;> simp [hop, isInpOp, isConstOp] at h1' h2'
      rw [hsplit, Finset.card_union_of_disjoint hdisj]; rfl
    rw [← hUcard]
    have hsub : Ess.image Fin.val ⊆ U := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      have hiV : i.val ∈ Dplug.V := hess_in i hi
      refine Finset.mem_filter.mpr ⟨hiV, ?_⟩
      dsimp only [Dplug, opPlug]
      have hopi : Dtrim.op i.val = NodeOp.inp i := by
        simp [Dtrim, trimDag, Draw, opRaw, i.isLt]
      rw [hopi]
      dsimp only
      split_ifs <;> simp [isInpOp, isConstOp]
    have hcard_img : (Ess.image Fin.val).card = Ess.card :=
      Finset.card_image_of_injective _ Fin.val_injective
    rw [← hcard_img]
    exact Finset.card_le_card hsub
  have hbeta_plug : beta1 Dplug.V (dagEdges Dplug.V Dplug.op) + Ess.card ≤ binary C + 1 := by
    have h1 := beta1_add_card (dagEdges_allIn Dplug)
    have h2 := dag_edge_vertex_identity Dplug.V Dplug.op
    rw [hcc_plug] at h1
    omega
  rcases reduce_to_normal_form Dplug hnc_plug with ⟨Dnf, hnf, hbeta_nf, hneg_nf, heval_nf⟩
  have hcc_nf : cc Dnf.V (dagEdges Dnf.V Dnf.op) = 1 := by
    have hteq : (trimDag Dnf).V = Dnf.V := by
      ext x; simp only [trimDag, Finset.mem_filter, and_iff_left_iff_imp]; exact hnf.1 x
    have h1 := trimDag_connected Dnf
    change cc (trimDag Dnf).V (dagEdges (trimDag Dnf).V Dnf.op) = 1 at h1
    rwa [hteq] at h1
  have hconst_nf : constCount Dnf.V Dnf.op = 0 := by
    dsimp only [constCount]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v hv
    exact (hnf.2 v hv).1
  have hinp_nf_le : inpCount Dnf.V Dnf.op ≤ k := by
    let S := Dnf.V.filter (fun v => isInpOp (Dnf.op v))
    let toFin : ℕ → Fin k := fun v =>
      match Dnf.op v with
      | NodeOp.inp j => j
      | _ => ⟨0, by
          by_contra hk0
          have hk_eq : k = 0 := by omega
          subst hk_eq
          rcases hnc_plug with ⟨y1, y2, hne⟩
          have : y1 = y2 := funext (fun i => Fin.elim0 i)
          exact hne (by rw [this])⟩
    have hinj : Set.InjOn toFin (S : Set ℕ) := by
      intro v1 hv1 v2 hv2 heq
      have h1 := Finset.mem_filter.mp hv1
      have h2 := Finset.mem_filter.mp hv2
      cases hop1 : Dnf.op v1 with
      | inp j1 =>
        cases hop2 : Dnf.op v2 with
        | inp j2 =>
          have hj : j1 = j2 := by simpa [toFin, hop1, hop2] using heq
          subst hj
          exact Dnf.hinp_inj v1 h1.1 v2 h2.1 j1 hop1 hop2
        | const _ => simp [hop2, isInpOp] at h2
        | copy _ => simp [hop2, isInpOp] at h2
        | neg _ => simp [hop2, isInpOp] at h2
        | bin _ _ _ => simp [hop2, isInpOp] at h2
      | const _ => simp [hop1, isInpOp] at h1
      | copy _ => simp [hop1, isInpOp] at h1
      | neg _ => simp [hop1, isInpOp] at h1
      | bin _ _ _ => simp [hop1, isInpOp] at h1
    have hcard : S.card = (S.image toFin).card := (Finset.card_image_of_injOn hinj).symm
    calc inpCount Dnf.V Dnf.op = (S.image toFin).card := hcard
      _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_univ _
      _ = k := by simp
  have hbin_nf_eq : binCount Dnf.V Dnf.op + 1 = beta1 Dnf.V (dagEdges Dnf.V Dnf.op) + inpCount Dnf.V Dnf.op := by
    have h1 := beta1_add_card (dagEdges_allIn Dnf)
    have h2 := dag_edge_vertex_identity Dnf.V Dnf.op
    rw [hcc_nf] at h1
    rw [hconst_nf] at h2
    omega
  rcases normal_form_to_circuit Dnf hnf with ⟨G, hGfan, hGinv, hGbin, hGeval⟩
  refine ⟨G, hGfan, ?_, ?_, ?_⟩
  · change G.size - inv G + Ess.card ≤ binary C + k
    dsimp only [inv]
    rw [hGbin]
    omega
  · change inv G ≤ inv C
    dsimp only [inv]
    rw [hGinv]
    exact hneg_nf.trans hneg_plug_le
  · intro y
    rw [hGeval y, heval_nf y, heval_plug_out y]

end PEqualNP.Outside.L_clb_127.X586

namespace PEqualNP.Outside.L_clb_127
theorem T586 : (∀ (n k : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.MetaComplexity.FanInTwo C →
  let inv := fun (G : PEqualNP.CircuitLowerBounds.Circuit) =>
    (G.gates.filter (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length
  let binary := fun (G : PEqualNP.CircuitLowerBounds.Circuit) => G.size - inv G
  let f := fun (x : Fin n → Bool) => C.eval (List.ofFn x)
  let e := ((Finset.univ : Finset (Fin n)).filter (fun i =>
    ∃ x : Fin n → Bool, f (Function.update x i false) ≠ f (Function.update x i true))).card
  ∀ (wire : Fin k → Fin n) (fixed : Fin n → Bool), Function.Injective wire →
    let plug := fun (y : Fin k → Bool) (i : Fin n) =>
      if i ∈ Finset.univ.image wire then decide (∃ j, wire j = i ∧ y j = true) else fixed i
    (∃ x y : Fin k → Bool, f (plug x) ≠ f (plug y)) →
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧
      binary D + e ≤ binary C + k ∧ inv D ≤ inv C ∧
      ∀ y : Fin k → Bool, D.eval (List.ofFn y) = f (plug y)) := by
  intro n k C hfan inv binary f e wire fixed hwinj plug hnc
  exact PEqualNP.Outside.L_clb_127.X586.solve_lib_586 n k C hfan wire fixed hwinj hnc

end PEqualNP.Outside.L_clb_127


namespace PEqualNP.Outside.L_clb_127.X25689.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_init (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_init [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_init gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_init gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)

def rv (w : List Bool) : Bool ⊕ ℕ → Bool
  | .inl b => b
  | .inr t => w.getD t false
theorem rv_ext (hs e : List Gate) (y : List Bool) (r : Bool ⊕ ℕ) (h : ∀ t, r = .inr t → t < y.length + hs.length) :
    rv (run (hs ++ e) y) r = rv (run hs y) r := by
  rcases r with b | t
  · rfl
  · exact run_init _ _ _ _ (h t rfl)

theorem gv (N : ℕ) (C : Circuit) (hb : ReadsBack N C) (x : List Bool) (hx : x.length = N) (j : ℕ)
    (hj : j < C.gates.length) :
    (run C.gates x).getD (N + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (run C.gates x).getD i false) := by
  have hw := run_gate C.gates x j hj
  have he : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  rw [hx, ← he] at hw
  rw [hw]
  congr 1
  exact List.map_congr_left fun i hi => if_pos (hb j hj i hi)

theorem past (gs : List Gate) (x : List Bool) (i : ℕ) (hi : x.length + gs.length ≤ i) :
    (run gs x).getD i false = false :=
  List.getD_eq_default _ _ (by rw [run_length]; exact hi)

theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (PEqualNP.Represents.oneEach u v).length = n + m := by
  simp [PEqualNP.Represents.oneEach]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_append_left (by simpa using h)]
    simp only [List.getElem?_ofFn]
    simp [h, Fin.ext_iff]
    omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem?_ofFn]
    by_cases h2 : i - n < m
    · simp [h2, Fin.ext_iff]
      have hu : ¬ i = u.val := by omega
      by_cases hv : i = n + v.val
      · simp [hv]
      · have hv' : ¬ i - n = v.val := by omega
        simp [hu, hv, hv']
    · simp [h2]
      omega

theorem sa_val {n : ℕ} (u : Fin (n + 1)) (a : Fin n) :
    ((u.succAbove a : Fin (n + 1)) : ℕ) = if (a : ℕ) < u then (a : ℕ) else a + 1 := by
  by_cases h : (a : ℕ) < u
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]; simp [h]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)]; simp [h]

def reads (g : Gate) (w : ℕ) : Prop :=
  (g.op = .not ∧ g.inputs.head? = some w) ∨ (g.op ≠ .not ∧ w ∈ g.inputs)

def Good (P : Prop) (g : Gate) : Prop :=
  ((g.op = .not ∧ ∃ a, g.inputs = [a]) ∨
    ((g.op = .and ∨ g.op = .or) ∧ ∃ a b, a ≠ b ∧ g.inputs = [a,b])) ∧
    (P → g.op = .and ∨ g.op = .or)

theorem good_shape {P : Prop} {g : Gate} (h : Good P g) :
    (g.op = .not → g.inputs.length = 1) ∧
    (g.op ≠ .not → g.inputs.length = 2 ∧ g.inputs.Nodup) := by
  rcases h.1 with ⟨ho,a,ha⟩ | ⟨ho,a,b,hn,ha⟩
  · simp [ho,ha]
  · rcases ho with ho|ho <;> simp [ho,ha,hn]

theorem good_fan {P : Prop} {C : Circuit} (h : ∀ g ∈ C.gates, Good P g) : FanInTwo C := by
  intro g hg
  rcases (h g hg).1 with ⟨ho,a,ha⟩ | ⟨ho,a,b,_,ha⟩
  · simp [ho,ha]
  · rcases ho with ho|ho <;> simp [ho,ha]

theorem good_mono {P : Prop} {C : Circuit} (h : ∀ g ∈ C.gates, Good P g) :
    P → Monotone2 C := by
  intro p g hg
  exact ⟨by simpa using (h g hg).2 p,(good_fan h g hg).2⟩

theorem good_read {P : Prop} {g : Gate} (h : Good P g) (w : ℕ) : reads g w ↔ w ∈ g.inputs := by
  rcases h.1 with ⟨ho,a,ha⟩ | ⟨ho,a,b,_,ha⟩
  · simp [reads,ho,ha,eq_comm]
  · rcases ho with ho|ho <;> simp [reads,ho]

end PEqualNP.Outside.L_clb_127.X25689.Normalize

namespace PEqualNP.Outside.L_clb_127.X25689.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem emit (P : Prop) (N : ℕ) (hs : List Gate) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hmon : P → op = GateOp.and ∨ op = GateOp.or)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) (hv : ∀ r ∈ rs, ∀ t, r = .inr t → t < N + hs.length) :
    ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, Good P g) ∧
      (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
      ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
  have keep : ∀ r : Bool ⊕ ℕ, (∀ t, r = .inr t → t < N + hs.length) → (∀ y : List Bool, y.length = N → rv (run hs y) r = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, Good P g) ∧
        (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro r h1 h2
    exact ⟨r, [], by simp, by simp, by simp, by simpa using h1, fun y hy => by rw [List.append_nil]; exact h2 y hy⟩
  have add : ∀ g : Gate, Good P g → (∀ t ∈ g.inputs, t < N + hs.length) →
      (∀ y : List Bool, y.length = N → g.op.eval (g.inputs.map fun i => (run hs y).getD i false) = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, Good P g) ∧
        (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro g h1 h1' h2
    refine ⟨.inr (N + hs.length), [g], by simp, by simpa using h1, by simpa using h1', ?_, fun y hy => ?_⟩
    · intro t ht
      cases ht
      simp
    · have : N + hs.length = (run hs y).length := by rw [run_length, hy]
      simp only [rv]
      rw [run_snoc, this, getD_at]
      exact h2 y hy
  by_cases hn : op = GateOp.not
  · subst op
    rcases rs with _ | ⟨r, rs⟩
    · exact keep (.inl true) (by simp) (by intro y hy; rfl)
    · have hr := hv r (by simp)
      rcases r with b | t
      · exact keep (.inl (!b)) (by simp) (by intro y hy; rfl)
      · exact add ⟨.not,[t]⟩ ⟨Or.inl ⟨rfl,t,rfl⟩,hmon⟩ (by simpa using hr t rfl)
          (by intro y hy; rfl)
  have hop' : op = GateOp.and ∨ op = GateOp.or := by tauto
  rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨u, rs⟩⟩⟩
  · rcases hop' with rfl | rfl
    · exact keep (.inl true) (by simp) (by intro y _; rfl)
    · exact keep (.inl false) (by simp) (by intro y _; rfl)
  · have hr := hv r (by simp)
    rcases hop' with rfl | rfl
    · exact keep r hr (by intro y _; simp [GateOp.eval])
    · exact keep r hr (by intro y _; simp [GateOp.eval])
  · have hr := hv r (by simp)
    have hs' := hv s (by simp)
    rcases hop' with rfl | rfl
    · rcases r with b | t
      · cases b
        · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
        · by_cases same : t=q
          · subst q
            exact keep (.inr t) hr (by intro y _; simp [GateOp.eval,rv])
          · exact add ⟨GateOp.and,[t,q]⟩ ⟨Or.inr ⟨Or.inl rfl,t,q,same,rfl⟩,fun _ => Or.inl rfl⟩
              (by simp; exact ⟨hr t rfl, hs' q rfl⟩) (by intro y _; simp [GateOp.eval,rv])
    · rcases r with b | t
      · cases b
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
        · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · by_cases same : t=q
          · subst q
            exact keep (.inr t) hr (by intro y _; simp [GateOp.eval,rv])
          · exact add ⟨GateOp.or,[t,q]⟩ ⟨Or.inr ⟨Or.inr rfl,t,q,same,rfl⟩,fun _ => Or.inr rfl⟩
              (by simp; exact ⟨hr t rfl, hs' q rfl⟩) (by intro y _; simp [GateOp.eval,rv])
  · simp at hl

theorem engine {X : Type} (P : Prop) (n M : ℕ) (C : Circuit) (src tgt : X → List Bool) (hsrc : ∀ x, (src x).length = n) (htgt : ∀ x, (tgt x).length = M) (F : Finset ℕ)
    (hC : FanInTwo C) (hmon : P → Monotone2 C)
    (h0 : ∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false)
    (hne : ¬∃ b, ∀ x, C.eval (src x) = b)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
      ∃ w < n + j, ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false)) :
    ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧ D.size + F.card ≤ C.size ∧
      ∀ x, D.eval (tgt x) = C.eval (src x) := by
  classical
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, Good P g) ∧
      (∀ i (hi : i < hs.length), ∀ t ∈ hs[i].inputs, t < M + i) ∧
      hs.length + (F.filter fun j => j < k).card ≤ k ∧
      (∀ w t, w < n + k → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + k, (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if h : ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false then .inr h.choose else if hb : ∃ b, ∀ x, (src x).getD w false = b then .inl hb.choose else .inl false, by simp, by simp, by simp, ?_, ?_⟩
      · intro w t hw ht
        beta_reduce at ht
        split_ifs at ht with h1 h2
        cases ht
        simpa using h1.choose_spec.1
      · intro x w hw
        simp only [Nat.add_zero] at hw
        rw [run_input _ _ _ (by rw [hsrc]; exact hw)]
        beta_reduce
        split_ifs with h1 h2
        · exact h1.choose_spec.2 x
        · exact h2.choose_spec x
        · rcases h0 w hw with h | h
          · exact absurd h h2
          · exact absurd h h1
    | succ k ih =>
      intro hk
      obtain ⟨hs, m, h1, h5, h2, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      have fin : ∀ (r : Bool ⊕ ℕ) (e : List Gate), (∀ g ∈ e, Good P g) → (∀ g ∈ e, ∀ t ∈ g.inputs, t < M + hs.length) →
          (∀ t, r = .inr t → t < M + hs.length + e.length) → e.length + (if k ∈ F then 1 else 0) ≤ 1 →
          (∀ x : X, (run C.gates (src x)).getD (n + k) false = rv (run (hs ++ e) (tgt x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, Good P g) ∧
      (∀ i (hi : i < hs.length), ∀ t ∈ hs[i].inputs, t < M + i) ∧
      hs.length + (F.filter fun j => j < k + 1).card ≤ k + 1 ∧
      (∀ w t, w < n + (k + 1) → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + (k + 1), (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
        intro r e he he' hr hlen hval
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · exact he g hg
        · intro i hi t ht
          rw [List.getElem_append] at ht
          split_ifs at ht with hih
          · exact h5 i hih t ht
          · have hmem : e[i - hs.length]'(by simp at hi; omega) ∈ e := List.mem_iff_getElem.mpr ⟨_, _, rfl⟩
            have := he' _ hmem t ht
            omega
        · have e1 : (F.filter fun j => j < k + 1) ⊆ (F.filter fun j => j < k) ∪ (if k ∈ F then {k} else ∅) := by
            intro j hj
            rw [Finset.mem_filter] at hj
            rcases Nat.lt_or_ge j k with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj.1, h⟩)
            · have : j = k := by omega
              subst this
              rw [if_pos hj.1]; simp
          have e2 := (Finset.card_le_card e1).trans (Finset.card_union_le _ _)
          rw [List.length_append]
          by_cases hkF : k ∈ F
          · rw [if_pos hkF] at e2 hlen
            rw [Finset.card_singleton] at e2
            omega
          · rw [if_neg hkF] at e2 hlen
            rw [Finset.card_empty] at e2
            omega
        · intro w t hw ht
          rw [List.length_append]
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self] at ht
            have := hr t ht; omega
          · rw [Function.update_of_ne hwe] at ht
            have := h3 w t (by omega) ht; omega
        · intro x w hw
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self]; exact hval x
          · rw [Function.update_of_ne hwe, h4 x w (by omega)]
            refine (rv_ext hs e (tgt x) (m w) fun t ht => ?_).symm
            have := h3 w t (by omega) ht
            rw [htgt]; exact this
      by_cases hkF : k ∈ F
      · rcases (hF k hkF).2 with ⟨b, hb⟩ | ⟨w, hw, hb⟩
        · exact fin (.inl b) [] (by simp) (by simp) (by simp) (by simp [hkF]) (fun x => hb x)
        · refine fin (m w) [] (by simp) (by simp) (fun t ht => by simpa using h3 w t hw ht) (by simp [hkF]) (fun x => ?_)
          rw [List.append_nil, ← h4 x w hw]
          exact hb x
      · have hg := hC _ (List.getElem_mem hk')
        have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or ∨ C.gates[k].op = GateOp.not := by simpa using hg.1
        let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else .inl false
        obtain ⟨r, e, e1, e2, e2', e3, e4⟩ := emit P M hs C.gates[k].op hop (fun p => by simpa using (hmon p _ (List.getElem_mem hk')).1) (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
          simp only [m'] at ht
          split_ifs at ht with h
          exact h3 i t h ht)
        refine fin r e e2 e2' e3 (by simp [hkF]; exact e1) (fun x => ?_)
        rw [e4 _ (htgt x)]
        have rg := run_gate C.gates (src x) k hk'
        rw [hsrc] at rg
        rw [rg, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp, m']
        split_ifs with h
        · exact h4 x i h
        · rfl
  obtain ⟨hs, m, h1, h5, h2, h3, h4⟩ := key C.gates.length le_rfl
  have hFc : (F.filter fun j => j < C.gates.length) = F := Finset.filter_true_of_mem fun j hj => (hF j hj).1
  rw [hFc] at h2
  have hout : C.output < n + C.gates.length := by
    by_contra h
    refine hne ⟨false, fun x => ?_⟩
    change (run C.gates (src x)).getD C.output false = false
    rw [List.getD_eq_default _ _ (by rw [run_length, hsrc]; omega)]
  have hev : ∀ x, C.eval (src x) = rv (run hs (tgt x)) (m C.output) := fun x => h4 x _ hout
  rcases hm : m C.output with b | t
  · exact absurd ⟨b, fun x => by rw [hev, hm]; rfl⟩ hne
  · refine ⟨⟨hs, t⟩, ?_, ?_, h2, fun x => ?_⟩
    · exact h1
    · intro j hj i hi
      have hj' : j < hs.length := hj
      have he : gateAt ⟨hs, t⟩ j = hs[j] := List.getD_eq_getElem _ _ hj'
      rw [he] at hi
      exact h5 j hj' i hi
    · have := hev x
      rw [hm] at this
      exact this.symm

end PEqualNP.Outside.L_clb_127.X25689.Normalize

namespace PEqualNP.Outside.L_clb_127.X25689.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def collapses {X : Type} (W : X → ℕ → Bool) (top : ℕ) (out : X → Bool) : Prop :=
  (∃ b, ∀ x, out x = b) ∨ ∃ w < top, ∀ x, out x = W x w

theorem read_pair (l : List ℕ) (w : ℕ) (hlen : l.length ≤ 2) (hw : w ∈ l) :
    l = [w] ∨ ∃ v, l = [w,v] ∨ l = [v,w] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨d,tail⟩⟩⟩
  · simp at hw
  · have e : w=a := by simpa using hw
    exact Or.inl (by rw [e])
  · rcases List.mem_cons.mp hw with e | h
    · exact Or.inr ⟨b,Or.inl (by rw [e])⟩
    · have e : w=b := by simpa using h
      exact Or.inr ⟨a,Or.inr (by rw [e])⟩
  · simp at hlen

theorem not_value {X : Type} (W : X → ℕ → Bool) (g : Gate) {w : ℕ} {b : Bool}
    (op : g.op = .not) (r : reads g w) (fixed : ∀ x, W x w = b) (x : X) :
    g.op.eval (g.inputs.map (W x)) = !b := by
  have he : g.inputs.head? = some w := by simpa [reads,op] using r
  cases h : g.inputs with
  | nil => simp [h] at he
  | cons a tail =>
    have e : a=w := by simpa [h] using he
    simp [op,h,GateOp.eval,e,fixed]

theorem dominant {X : Type} (W : X → ℕ → Bool) (g : Gate) (w : ℕ)
    (hlen : g.inputs.length ≤ 2) (r : reads g w) (op : g.op = .and ∨ g.op = .not)
    (fixed : ∀ x, W x w = false) :
    ∃ b, ∀ x, g.op.eval (g.inputs.map (W x)) = b := by
  rcases op with h|h
  · have mem : w ∈ g.inputs := by simpa [reads,h] using r
    refine ⟨false,fun x => ?_⟩
    rcases read_pair _ w hlen mem with e | ⟨v,e|e⟩ <;> simp [h,e,GateOp.eval,fixed]
  · exact ⟨true,not_value W g h r fixed⟩

theorem when_read {X : Type} (W : X → ℕ → Bool) (g : Gate) (top w : ℕ) (b : Bool)
    (ok : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hlen : g.inputs.length ≤ 2)
    (before : ∀ t ∈ g.inputs, t < top) (r : reads g w) (fixed : ∀ x, W x w = b) :
    collapses W top (fun x => g.op.eval (g.inputs.map (W x))) := by
  by_cases hn : g.op = .not
  · exact Or.inl ⟨!b,not_value W g hn r fixed⟩
  have hop : g.op = .and ∨ g.op = .or := by tauto
  have mem : w ∈ g.inputs := by simpa [reads,hn] using r
  rcases read_pair _ w hlen mem with e | ⟨v,e⟩
  · refine Or.inl ⟨b,fun x => ?_⟩
    rcases hop with ho|ho <;> simp [ho,e,GateOp.eval,fixed]
  · have hv : v < top := before v (by rcases e with h|h <;> simp [h])
    rcases hop with h|h
    · cases b
      · refine Or.inl ⟨false,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]
      · refine Or.inr ⟨v,hv,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]
    · cases b
      · refine Or.inr ⟨v,hv,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]
      · refine Or.inl ⟨true,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]

def toNat {s : ℕ} (K : Finset (Fin s)) : Finset ℕ := K.map ⟨Fin.val,Fin.val_injective⟩

theorem marked {X : Type} (N : ℕ) (C : Circuit) (src : X → List Bool)
    (hs : ∀ x, (src x).length=N) (u : ℕ) (hu : u<N) (hu0 : ∀ x, (src x).getD u false=false)
    (fan : FanInTwo C) (back : ReadsBack N C) (K : Finset (Fin C.gates.length))
    (mark : ∀ j ∈ K, reads (C.gates.get j) u ∨ ∃ i : Fin C.gates.length, i<j ∧
      reads (C.gates.get i) u ∧ ((C.gates.get i).op=.and ∨ (C.gates.get i).op=.not) ∧
      reads (C.gates.get j) (N+i.val)) :
    ∀ k ∈ toNat K, k < C.gates.length ∧
      collapses (fun x w => (run C.gates (src x)).getD w false) (N+k)
        (fun x => (run C.gates (src x)).getD (N+k) false) := by
  let W := fun (x : X) (w : ℕ) => (run C.gates (src x)).getD w false
  have raw (x : X) : W x u = false :=
    (run_input _ _ _ (by rw [hs]; exact hu)).trans (hu0 x)
  have atGate (j : Fin C.gates.length) : gateAt C j.val=C.gates.get j :=
    List.getD_eq_getElem _ _ j.isLt
  have ev (j : Fin C.gates.length) (x : X) :
      W x (N+j.val) = (C.gates.get j).op.eval ((C.gates.get j).inputs.map (W x)) := by
    simpa only [W,atGate j] using gv N C back (src x) (hs x) j.val j.isLt
  intro k hk
  obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hk
  refine ⟨j.isLt,?_⟩
  change collapses W (N+j.val) (fun x => W x (N+j.val))
  have same := funext (ev j)
  rw [same]
  have ok := fan (C.gates.get j) (List.get_mem _ _)
  have before (t : ℕ) (ht : t∈(C.gates.get j).inputs) : t<N+j.val :=
    back j.val j.isLt t (by rwa [atGate])
  have folded (w : ℕ) (b : Bool) (r : reads (C.gates.get j) w) (h : ∀ x, W x w=b) :=
    when_read W _ (N+j.val) w b (by simpa using ok.1) ok.2 before r h
  rcases mark j hj with direct | ⟨i,_,ri,oi,rj⟩
  · exact folded u false direct raw
  · have fi := fan (C.gates.get i) (List.get_mem _ _)
    obtain ⟨b,hb⟩ := dominant W _ u fi.2 ri oi raw
    exact folded (N+i.val) b rj (fun x => (ev i x).trans (hb x))

end PEqualNP.Outside.L_clb_127.X25689.Normalize

namespace PEqualNP.Outside.L_clb_127.X25689.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def oldFace {n m : ℕ} (u : Fin (n+1)) (x : List Bool) : Option (Fin n × Fin m) → List Bool
  | none => x
  | some p => oneEach (u.succAbove p.1) p.2

def newFace {n m : ℕ} (u : Fin (n+1)) (x : List Bool) : Option (Fin n × Fin m) → List Bool
  | none => List.ofFn (fun j : Fin (n+m) => x.getD (if j.val<u.val then j.val else j.val+1) false)
  | some p => oneEach p.1 p.2

theorem old_len {n m : ℕ} (u : Fin (n+1)) (x : List Bool) (hx : x.length=n+1+m)
    (p : Option (Fin n × Fin m)) : (oldFace u x p).length=n+1+m := by
  cases p <;> simp [oldFace,oneEach_length,hx]

theorem new_len {n m : ℕ} (u : Fin (n+1)) (x : List Bool)
    (p : Option (Fin n × Fin m)) : (newFace u x p).length=n+m := by
  cases p <;> simp [newFace,oneEach_length]

theorem off_face {n m : ℕ} (u : Fin (n+1)) (x : List Bool) (hx : x.getD u.val false=false)
    (p : Option (Fin n × Fin m)) : (oldFace u x p).getD u.val false=false := by
  cases p with
  | none => exact hx
  | some p =>
    simp only [oldFace,oneEach_getD,decide_eq_false_iff_not,sa_val]
    have := u.isLt
    split_ifs <;> omega

theorem face_inputs {n m : ℕ} (u : Fin (n+1)) (x : List Bool) (hx : x.getD u.val false=false)
    (w : ℕ) (hw : w<n+1+m) :
    (∃ b, ∀ p : Option (Fin n × Fin m), (oldFace u x p).getD w false = b) ∨
    ∃ t, t<n+m ∧ ∀ p : Option (Fin n × Fin m), (oldFace u x p).getD w false =
      (newFace u x p).getD t false := by
  have hu := u.isLt
  rcases lt_trichotomy w u.val with h | h | h
  · have ht : w<n+m := by omega
    refine Or.inr ⟨w,ht,?_⟩
    intro p
    cases p with
    | none => simp [oldFace,newFace,ht,h]
    | some p =>
      have := p.1.isLt
      have := p.2.isLt
      simp only [oldFace,newFace,oneEach_getD,decide_eq_decide,sa_val]
      split_ifs <;> omega
  · subst w
    exact Or.inl ⟨false,off_face u x hx⟩
  · have ht : w-1<n+m := by omega
    have hn : ¬ w-1<u.val := by omega
    have eq : w-1+1=w := by omega
    refine Or.inr ⟨w-1,ht,?_⟩
    intro p
    cases p with
    | none => simp [oldFace,newFace,ht,hn,eq]
    | some p =>
      have := p.1.isLt
      have := p.2.isLt
      simp only [oldFace,newFace,oneEach_getD,decide_eq_decide,sa_val]
      split_ifs <;> omega

end PEqualNP.Outside.L_clb_127.X25689.Normalize

namespace PEqualNP.Outside.L_clb_127.X25689.Normalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private theorem blank_dead_signed (P : Prop) (N : ℕ) (C : Circuit)
    (hc : FanInTwo C) (hm : P → Monotone2 C) (hb : ReadsBack N C)
    (j : ℕ) (hj : j < C.gates.length)
    (hdead : ∀ k < C.gates.length, N + j ∉ (gateAt C k).inputs) (ho : C.output ≠ N + j) :
    let E : Circuit := ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩
    FanInTwo E ∧ (P → Monotone2 E) ∧ ReadsBack N E ∧ E.size = C.size ∧
      (∀ x : List Bool, x.length = N → E.eval x = C.eval x) ∧
      (∀ x : List Bool, x.length = N → (run E.gates x).getD (N + j) false = false) := by
  let E : Circuit := ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩
  have hlen : E.gates.length = C.gates.length := by simp [E]
  have hg : ∀ k, gateAt E k = if k = j then ⟨GateOp.or, []⟩ else gateAt C k := by
    intro k
    simp only [gateAt, E, List.getD_eq_getElem?_getD, List.getElem?_set]
    by_cases hk : k = j
    · subst hk; simp [hj]
    · simp [hk, Ne.symm hk]
  have hc' : FanInTwo E := by
    intro g h
    rcases List.mem_or_eq_of_mem_set h with h | h
    · exact hc g h
    · subst h; simp
  have hm' : P → Monotone2 E := by
    intro hP g h
    rcases List.mem_or_eq_of_mem_set h with h | h
    · exact hm hP g h
    · subst h; simp
  have hb' : ReadsBack N E := by
    intro k hk i hi
    rw [hg] at hi
    split_ifs at hi with h
    · simp at hi
    · exact hb k (by rw [hlen] at hk; exact hk) i hi
  have agree : ∀ x : List Bool, x.length = N → ∀ i, i ≠ N + j →
      (run E.gates x).getD i false = (run C.gates x).getD i false := by
    intro x hx i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases hlo : i < N
      · rw [run_input _ _ _ (by omega), run_input _ _ _ (by omega)]
      by_cases hhi : N + C.gates.length ≤ i
      · rw [past _ _ _ (by rw [hlen]; omega), past _ _ _ (by omega)]
      have hk : i - N < C.gates.length := by omega
      have hik : i = N + (i - N) := by omega
      rw [hik, gv N E hb' x hx _ (by rw [hlen]; exact hk), gv N C hb x hx _ hk, hg,
        if_neg (by omega)]
      congr 1
      refine List.map_congr_left fun i' hi' => ih i' ?_ ?_
      · have := hb _ hk i' hi'; omega
      · rintro rfl; exact hdead _ hk hi'
  refine ⟨hc', hm', hb', hlen, fun x hx => agree x hx _ ho, fun x hx => ?_⟩
  change (run E.gates x).getD (N + j) false = false
  rw [gv N E hb' x hx j (by rw [hlen]; exact hj), hg, if_pos rfl]
  simp [GateOp.eval]

theorem finish_live {X : Type} (P : Prop) (M : ℕ) (y : X → List Bool)
    (hy : ∀ x, (y x).length = M) (f : X → Bool)
    (hnc : ¬ ∃ b : Bool, ∀ x, f x = b) (C : Circuit)
    (hg : ∀ g ∈ C.gates, Good P g) (hb : ReadsBack M C) (hf : ∀ x, C.eval (y x) = f x) :
    ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧ D.size ≤ C.size ∧
      (∀ x, D.eval (y x) = f x) ∧
      ∀ i : Fin D.gates.length, M + i.val ≠ D.output →
        ∃ j : Fin D.gates.length, i < j ∧ reads (D.gates.get j) (M + i.val) := by
  classical
  have hex : ∃ k, ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧
      D.size ≤ k ∧ ∀ x, D.eval (y x) = f x := ⟨C.size, C, hg, hb, le_rfl, hf⟩
  obtain ⟨D, hgood, hback, hsize, hval⟩ := Nat.find_spec hex
  have hmin0 : Nat.find hex ≤ C.size := Nat.find_min' hex ⟨C, hg, hb, le_rfl, hf⟩
  refine ⟨D, hgood, hback, hsize.trans hmin0, hval, ?_⟩
  intro i hout
  by_contra hn
  have dead : ∀ k < D.gates.length, M + i.val ∉ (gateAt D k).inputs := by
    intro k hk hpin
    have hh := hback k hk _ hpin
    have later : i < (⟨k, hk⟩ : Fin D.gates.length) := by
      change i.val < k
      omega
    have eqg : D.gates.get ⟨k, hk⟩ = gateAt D k := (List.getD_eq_getElem _ _ hk).symm
    have hgk : Good P (D.gates.get ⟨k, hk⟩) := hgood _ (List.getElem_mem hk)
    have hread : reads (D.gates.get ⟨k, hk⟩) (M + i.val) ↔
        M + i.val ∈ (D.gates.get ⟨k, hk⟩).inputs := by
      apply good_read
      exact hgk
    exact hn ⟨⟨k, hk⟩, later, hread.2 (by rwa [eqg])⟩
  let E : Circuit := ⟨D.gates.set i.val ⟨GateOp.or, []⟩, D.output⟩
  have hdf : FanInTwo D := by apply good_fan; exact hgood
  have hdm : P → Monotone2 D := by
    intro hP
    apply good_mono <;> assumption
  obtain ⟨hef, hem, _, hes, heq, hzero⟩ :=
    blank_dead_signed P M D hdf hdm hback i.val i.isLt dead hout.symm
  have heval (x : X) : E.eval (y x) = f x := (heq _ (hy x)).trans (hval x)
  have hmarked : ∀ j ∈ ({i.val} : Finset ℕ), j < E.gates.length ∧
      ((∃ b, ∀ x, (run E.gates (y x)).getD (M + j) false = b) ∨
       ∃ w < M + j, ∀ x, (run E.gates (y x)).getD (M + j) false =
         (run E.gates (y x)).getD w false) := by
    intro j hj
    rw [Finset.mem_singleton] at hj
    subst j
    exact ⟨by simpa [E] using i.isLt, Or.inl ⟨false, fun x => hzero _ (hy x)⟩⟩
  obtain ⟨J, hJg, hJb, hJs, hJv⟩ := engine P M M E y y hy hy {i.val} hef hem
    (fun w hw => Or.inr ⟨w, hw, fun _ => rfl⟩)
    (fun ⟨b, h⟩ => hnc ⟨b, fun x => (heval x).symm.trans (h x)⟩) hmarked
  have lower : Nat.find hex ≤ J.size :=
    Nat.find_min' hex ⟨J, hJg, hJb, le_rfl, fun x => (hJv x).trans (heval x)⟩
  rw [Finset.card_singleton] at hJs
  change E.size = D.size at hes
  omega

end PEqualNP.Outside.L_clb_127.X25689.Normalize

namespace PEqualNP.Outside.L_clb_127.X25689.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical
noncomputable def listed (p : GateOp → Nat) (gs : List Gate) : Nat := (gs.map (fun g=>p g.op)).sum
noncomputable def remaining (p : GateOp → Nat) (C : Circuit) (F : Finset Nat) (k : Nat) : Nat :=
  ∑ j∈Finset.range k, if j∈F then 0 else p (gateAt C j).op

theorem full_price (p : GateOp → Nat) (C : Circuit) : remaining p C ∅ C.size=listed p C.gates := by
  have appendOne (l : List Gate) (g : Gate) : listed p (l++[g])=listed p l+p g.op := by
    simp [listed]
  have below (k : Nat) (h : k≤C.gates.length) : remaining p C ∅ k=listed p (C.gates.take k) := by
    induction k with
    | zero => simp [remaining,listed]
    | succ k ih =>
      have low : k<C.gates.length:=by omega
      rw [List.take_succ_eq_append_getElem low]
      change (∑j∈Finset.range (k+1),if j∈(∅ : Finset Nat) then 0 else p (gateAt C j).op)=_
      rw [Finset.sum_range_succ]
      change remaining p C ∅ k+_=_
      rw [ih (by omega)]
      rw [show gateAt C k=C.gates[k] from List.getD_eq_getElem _ _ low,appendOne] <;> simp
  simpa [Circuit.size] using below C.gates.length le_rfl

theorem blank_price (p : GateOp → Nat) (C : Circuit) (i : Fin C.gates.length) :
    let E : Circuit:=⟨C.gates.set i.val ⟨GateOp.or,[]⟩,C.output⟩
    remaining p E {i.val} E.size≤listed p C.gates := by
  intro E
  rw [←full_price p C]
  have sizes : E.size=C.size := by simp [E,Circuit.size]
  unfold remaining; rw [sizes]; apply Finset.sum_le_sum
  intro j hj
  have low : j<C.gates.length:=Finset.mem_range.mp hj
  have newer : j<E.gates.length := by simpa [E] using low
  by_cases same : j=i.val
  · simp [same]
  · have ne : i.val≠j:=Ne.symm same
    simp [E,gateAt,List.getD_eq_getElem _ _ low,List.getD_eq_getElem _ _ newer,low,same,ne,List.getElem_set]

theorem emission_price (p : GateOp → Nat) (e : List Gate) (op : GateOp) (len : e.length≤1) (same : ∀g∈e,g.op=op) :
    listed p e≤p op := by
  cases e with
  | nil => simp [listed]
  | cons g tail =>
    have h:=same g List.mem_cons_self
    have empty : tail=[] := List.length_eq_zero_iff.mp (by change tail.length+1≤1 at len;omega)
    subst tail; simp [listed,h]

theorem emitWeighted (P : Prop) (N : ℕ) (hs : List Gate) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hmon : P → op = GateOp.and ∨ op = GateOp.or)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) (hv : ∀ r ∈ rs, ∀ t, r = .inr t → t < N + hs.length) :
    ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g∈e,g.op=op) ∧ (∀ g ∈ e, Good P g) ∧
      (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
      ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
  have keep : ∀ r : Bool ⊕ ℕ, (∀ t, r = .inr t → t < N + hs.length) → (∀ y : List Bool, y.length = N → rv (run hs y) r = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g∈e,g.op=op) ∧ (∀ g ∈ e, Good P g) ∧
        (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro r h1 h2
    exact ⟨r, [], by simp, by simp, by simp, by simp, by simpa using h1, fun y hy => by rw [List.append_nil]; exact h2 y hy⟩
  have add : ∀ g : Gate, g.op=op → Good P g → (∀ t ∈ g.inputs, t < N + hs.length) →
      (∀ y : List Bool, y.length = N → g.op.eval (g.inputs.map fun i => (run hs y).getD i false) = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g∈e,g.op=op) ∧ (∀ g ∈ e, Good P g) ∧
        (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro g same h1 h1' h2
    refine ⟨.inr (N + hs.length), [g], by simp, by simpa using same, by simpa using h1, by simpa using h1', ?_, fun y hy => ?_⟩
    · intro t ht
      cases ht
      simp
    · have : N + hs.length = (run hs y).length := by rw [run_length, hy]
      simp only [rv]
      rw [run_snoc, this, getD_at]
      exact h2 y hy
  by_cases hn : op = GateOp.not
  · subst op
    rcases rs with _ | ⟨r, rs⟩
    · exact keep (.inl true) (by simp) (by intro y hy; rfl)
    · have hr := hv r (by simp)
      rcases r with b | t
      · exact keep (.inl (!b)) (by simp) (by intro y hy; rfl)
      · exact add ⟨.not,[t]⟩ rfl ⟨Or.inl ⟨rfl,t,rfl⟩,hmon⟩ (by simpa using hr t rfl)
          (by intro y hy; rfl)
  have hop' : op = GateOp.and ∨ op = GateOp.or := by tauto
  rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨u, rs⟩⟩⟩
  · rcases hop' with rfl | rfl
    · exact keep (.inl true) (by simp) (by intro y _; rfl)
    · exact keep (.inl false) (by simp) (by intro y _; rfl)
  · have hr := hv r (by simp)
    rcases hop' with rfl | rfl
    · exact keep r hr (by intro y _; simp [GateOp.eval])
    · exact keep r hr (by intro y _; simp [GateOp.eval])
  · have hr := hv r (by simp)
    have hs' := hv s (by simp)
    rcases hop' with rfl | rfl
    · rcases r with b | t
      · cases b
        · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
        · by_cases same : t=q
          · subst q
            exact keep (.inr t) hr (by intro y _; simp [GateOp.eval,rv])
          · exact add ⟨GateOp.and,[t,q]⟩ rfl ⟨Or.inr ⟨Or.inl rfl,t,q,same,rfl⟩,fun _ => Or.inl rfl⟩
              (by simp; exact ⟨hr t rfl, hs' q rfl⟩) (by intro y _; simp [GateOp.eval,rv])
    · rcases r with b | t
      · cases b
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
        · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · by_cases same : t=q
          · subst q
            exact keep (.inr t) hr (by intro y _; simp [GateOp.eval,rv])
          · exact add ⟨GateOp.or,[t,q]⟩ rfl ⟨Or.inr ⟨Or.inr rfl,t,q,same,rfl⟩,fun _ => Or.inr rfl⟩
              (by simp; exact ⟨hr t rfl, hs' q rfl⟩) (by intro y _; simp [GateOp.eval,rv])
  · simp at hl

theorem engineWeighted {X : Type} (P : Prop) (n M : ℕ) (C : Circuit) (src tgt : X → List Bool) (hsrc : ∀ x, (src x).length = n) (htgt : ∀ x, (tgt x).length = M) (F : Finset ℕ)
    (hC : FanInTwo C) (hmon : P → Monotone2 C)
    (h0 : ∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false)
    (hne : ¬∃ b, ∀ x, C.eval (src x) = b)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
      ∃ w < n + j, ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false)) :
    ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧ D.size + F.card ≤ C.size ∧ (∀ p, listed p D.gates≤remaining p C F C.size) ∧
      ∀ x, D.eval (tgt x) = C.eval (src x) := by
  classical
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, Good P g) ∧
      (∀ i (hi : i < hs.length), ∀ t ∈ hs[i].inputs, t < M + i) ∧
      hs.length + (F.filter fun j => j < k).card ≤ k ∧
      (∀ p, listed p hs≤remaining p C F (k)) ∧
      (∀ w t, w < n + k → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + k, (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if h : ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false then .inr h.choose else if hb : ∃ b, ∀ x, (src x).getD w false = b then .inl hb.choose else .inl false, by simp, by simp, by simp, by simp [listed,remaining], ?_, ?_⟩
      · intro w t hw ht
        beta_reduce at ht
        split_ifs at ht with h1 h2
        cases ht
        simpa using h1.choose_spec.1
      · intro x w hw
        simp only [Nat.add_zero] at hw
        rw [run_input _ _ _ (by rw [hsrc]; exact hw)]
        beta_reduce
        split_ifs with h1 h2
        · exact h1.choose_spec.2 x
        · exact h2.choose_spec x
        · rcases h0 w hw with h | h
          · exact absurd h h2
          · exact absurd h h1
    | succ k ih =>
      intro hk
      obtain ⟨hs, m, h1, h5, h2, spent, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      have fin : ∀ (r : Bool ⊕ ℕ) (e : List Gate), (∀ g ∈ e, Good P g) → (∀ g ∈ e, ∀ t ∈ g.inputs, t < M + hs.length) →
          (∀ t, r = .inr t → t < M + hs.length + e.length) → e.length + (if k ∈ F then 1 else 0) ≤ 1 →
          (∀ p, listed p e≤(if k∈F then 0 else p (gateAt C k).op)) →
          (∀ x : X, (run C.gates (src x)).getD (n + k) false = rv (run (hs ++ e) (tgt x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, Good P g) ∧
      (∀ i (hi : i < hs.length), ∀ t ∈ hs[i].inputs, t < M + i) ∧
      hs.length + (F.filter fun j => j < k + 1).card ≤ k + 1 ∧
      (∀ p, listed p hs≤remaining p C F (k + 1)) ∧
      (∀ w t, w < n + (k + 1) → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + (k + 1), (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
        intro r e he he' hr hlen charge hval
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · exact he g hg
        · intro i hi t ht
          rw [List.getElem_append] at ht
          split_ifs at ht with hih
          · exact h5 i hih t ht
          · have hmem : e[i - hs.length]'(by simp at hi; omega) ∈ e := List.mem_iff_getElem.mpr ⟨_, _, rfl⟩
            have := he' _ hmem t ht
            omega
        · have e1 : (F.filter fun j => j < k + 1) ⊆ (F.filter fun j => j < k) ∪ (if k ∈ F then {k} else ∅) := by
            intro j hj
            rw [Finset.mem_filter] at hj
            rcases Nat.lt_or_ge j k with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj.1, h⟩)
            · have : j = k := by omega
              subst this
              rw [if_pos hj.1]; simp
          have e2 := (Finset.card_le_card e1).trans (Finset.card_union_le _ _)
          rw [List.length_append]
          by_cases hkF : k ∈ F
          · rw [if_pos hkF] at e2 hlen
            rw [Finset.card_singleton] at e2
            omega
          · rw [if_neg hkF] at e2 hlen
            rw [Finset.card_empty] at e2
            omega
        · intro p
          change listed p (hs++e)≤remaining p C F (k+1)
          have lhs : listed p (hs++e)=listed p hs+listed p e := by simp [listed]
          rw [lhs,remaining,Finset.sum_range_succ]
          exact Nat.add_le_add (spent p) (charge p)
        · intro w t hw ht
          rw [List.length_append]
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self] at ht
            have := hr t ht; omega
          · rw [Function.update_of_ne hwe] at ht
            have := h3 w t (by omega) ht; omega
        · intro x w hw
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self]; exact hval x
          · rw [Function.update_of_ne hwe, h4 x w (by omega)]
            refine (rv_ext hs e (tgt x) (m w) fun t ht => ?_).symm
            have := h3 w t (by omega) ht
            rw [htgt]; exact this
      by_cases hkF : k ∈ F
      · rcases (hF k hkF).2 with ⟨b, hb⟩ | ⟨w, hw, hb⟩
        · exact fin (.inl b) [] (by simp) (by simp) (by simp) (by simp [hkF]) (by simp [listed,hkF]) (fun x => hb x)
        · refine fin (m w) [] (by simp) (by simp) (fun t ht => by simpa using h3 w t hw ht) (by simp [hkF]) (by simp [listed,hkF]) (fun x => ?_)
          rw [List.append_nil, ← h4 x w hw]
          exact hb x
      · have hg := hC _ (List.getElem_mem hk')
        have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or ∨ C.gates[k].op = GateOp.not := by simpa using hg.1
        let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else .inl false
        obtain ⟨r, e, e1, sameOps, e2, e2', e3, e4⟩ := emitWeighted P M hs C.gates[k].op hop (fun p => by simpa using (hmon p _ (List.getElem_mem hk')).1) (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
          simp only [m'] at ht
          split_ifs at ht with h
          exact h3 i t h ht)
        refine fin r e e2 e2' e3 (by simp [hkF]; exact e1) (by intro p; rw [if_neg hkF,show gateAt C k=C.gates[k] from List.getD_eq_getElem _ _ hk']; exact emission_price p e C.gates[k].op e1 sameOps) (fun x => ?_)
        rw [e4 _ (htgt x)]
        have rg := run_gate C.gates (src x) k hk'
        rw [hsrc] at rg
        rw [rg, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp, m']
        split_ifs with h
        · exact h4 x i h
        · rfl
  obtain ⟨hs, m, h1, h5, h2, spent, h3, h4⟩ := key C.gates.length le_rfl
  have hFc : (F.filter fun j => j < C.gates.length) = F := Finset.filter_true_of_mem fun j hj => (hF j hj).1
  rw [hFc] at h2
  have hout : C.output < n + C.gates.length := by
    by_contra h
    refine hne ⟨false, fun x => ?_⟩
    change (run C.gates (src x)).getD C.output false = false
    rw [List.getD_eq_default _ _ (by rw [run_length, hsrc]; omega)]
  have hev : ∀ x, C.eval (src x) = rv (run hs (tgt x)) (m C.output) := fun x => h4 x _ hout
  rcases hm : m C.output with b | t
  · exact absurd ⟨b, fun x => by rw [hev, hm]; rfl⟩ hne
  · refine ⟨⟨hs, t⟩, ?_, ?_, h2, spent, fun x => ?_⟩
    · exact h1
    · intro j hj i hi
      have hj' : j < hs.length := hj
      have he : gateAt ⟨hs, t⟩ j = hs[j] := List.getD_eq_getElem _ _ hj'
      rw [he] at hi
      exact h5 j hj' i hi
    · have := hev x
      rw [hm] at this
      exact this.symm

theorem finishWeighted {X : Type} (P : Prop) (M : ℕ) (y : X → List Bool)
    (hy : ∀ x, (y x).length = M) (f : X → Bool)
    (hnc : ¬ ∃ b : Bool, ∀ x, f x = b) (C : Circuit)
    (hg : ∀ g ∈ C.gates, Good P g) (hb : ReadsBack M C) (hf : ∀ x, C.eval (y x) = f x) :
    ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧ D.size ≤ C.size ∧ (∀ p, listed p D.gates≤listed p C.gates) ∧
      (∀ x, D.eval (y x) = f x) ∧
      ∀ i : Fin D.gates.length, M + i.val ≠ D.output →
        ∃ j : Fin D.gates.length, i < j ∧ reads (D.gates.get j) (M + i.val) := by
  classical
  have hex : ∃ k, ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧
      D.size ≤ k ∧ (∀ p, listed p D.gates≤listed p C.gates) ∧ ∀ x, D.eval (y x) = f x := ⟨C.size, C, hg, hb, le_rfl, fun _=>le_rfl, hf⟩
  obtain ⟨D, hgood, hback, hsize, hprice, hval⟩ := Nat.find_spec hex
  have hmin0 : Nat.find hex ≤ C.size := Nat.find_min' hex ⟨C, hg, hb, le_rfl, fun _=>le_rfl, hf⟩
  refine ⟨D, hgood, hback, hsize.trans hmin0, hprice, hval, ?_⟩
  intro i hout
  by_contra hn
  have dead : ∀ k < D.gates.length, M + i.val ∉ (gateAt D k).inputs := by
    intro k hk hpin
    have hh := hback k hk _ hpin
    have later : i < (⟨k, hk⟩ : Fin D.gates.length) := by
      change i.val < k
      omega
    have eqg : D.gates.get ⟨k, hk⟩ = gateAt D k := (List.getD_eq_getElem _ _ hk).symm
    have hgk : Good P (D.gates.get ⟨k, hk⟩) := hgood _ (List.getElem_mem hk)
    have hread : reads (D.gates.get ⟨k, hk⟩) (M + i.val) ↔
        M + i.val ∈ (D.gates.get ⟨k, hk⟩).inputs := by
      apply good_read
      exact hgk
    exact hn ⟨⟨k, hk⟩, later, hread.2 (by rwa [eqg])⟩
  let E : Circuit := ⟨D.gates.set i.val ⟨GateOp.or, []⟩, D.output⟩
  have hdf : FanInTwo D := by apply good_fan; exact hgood
  have hdm : P → Monotone2 D := by
    intro hP
    apply good_mono <;> assumption
  obtain ⟨hef, hem, _, hes, heq, hzero⟩ :=
    blank_dead_signed P M D hdf hdm hback i.val i.isLt dead hout.symm
  have heval (x : X) : E.eval (y x) = f x := (heq _ (hy x)).trans (hval x)
  have hmarked : ∀ j ∈ ({i.val} : Finset ℕ), j < E.gates.length ∧
      ((∃ b, ∀ x, (run E.gates (y x)).getD (M + j) false = b) ∨
       ∃ w < M + j, ∀ x, (run E.gates (y x)).getD (M + j) false =
         (run E.gates (y x)).getD w false) := by
    intro j hj
    rw [Finset.mem_singleton] at hj
    subst j
    exact ⟨by simpa [E] using i.isLt, Or.inl ⟨false, fun x => hzero _ (hy x)⟩⟩
  obtain ⟨J, hJg, hJb, hJs, hpriceJ, hJv⟩ := engineWeighted P M M E y y hy hy {i.val} hef hem
    (fun w hw => Or.inr ⟨w, hw, fun _ => rfl⟩)
    (fun ⟨b, h⟩ => hnc ⟨b, fun x => (heval x).symm.trans (h x)⟩) hmarked
  have lower : Nat.find hex ≤ J.size :=
    Nat.find_min' hex ⟨J, hJg, hJb, le_rfl, fun p=>(hpriceJ p).trans ((blank_price p D i).trans (hprice p)), fun x => (hJv x).trans (heval x)⟩
  rw [Finset.card_singleton] at hJs
  change E.size = D.size at hes
  omega

end PEqualNP.Outside.L_clb_127.X25689.Normalize

namespace PEqualNP.Outside.L_clb_127.X25689
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical

def FixedAt {X : Type} (W : X → Nat → Bool) (i : Nat) := ∃ b, ∀ x, W x i = b
noncomputable def inputsFixed {X : Type} (W : X → Nat → Bool) (g : Gate) :=
  g.inputs.toFinset.filter (FixedAt W)
noncomputable def eliminated {X : Type} (N : Nat) (C : Circuit) (W : X → Nat → Bool) :=
  (Finset.range C.size).filter (fun j=> FixedAt W (N+j) ∨ ∃ i∈(gateAt C j).inputs, FixedAt W i)
noncomputable def bin (op : GateOp) : Nat := if op=.not then 0 else 1
noncomputable def inv (op : GateOp) : Nat := if op=.not then 1 else 0

theorem countLocal {X : Type} (W : X → Nat → Bool) (g : Gate) (o : Nat)
    (shape : Good False g) (evaluate : ∀x, W x o=g.op.eval (g.inputs.map (W x))) :
    (inputsFixed W g).card ≤ (if FixedAt W o then 1 else 0)+
      (if FixedAt W o ∨ ∃ i∈g.inputs, FixedAt W i then bin g.op else 0) := by
  classical
  have singleton (i : Nat) : (Finset.filter (FixedAt W) {i}) = (if FixedAt W i then {i} else ∅) := by
    by_cases h : FixedAt W i <;> ext v <;> simp [h] <;> aesop
  rcases shape.1 with ⟨op,a,inputs⟩|⟨op,a,b,ab,inputs⟩
  · by_cases ha : FixedAt W a
    · obtain ⟨v,hv⟩:=ha
      have fa : FixedAt W a:=⟨v,hv⟩
      have out : FixedAt W o:=⟨!v,fun x=>by simp [evaluate x,op,inputs,GateOp.eval,hv]⟩
      simp [inputsFixed,inputs,singleton,fa,out,bin,op]
    · simp [inputsFixed,inputs,singleton,ha]
  · have budget : bin g.op=1 := by rcases op with e|e <;> simp [bin,e]
    by_cases fa : FixedAt W a <;> by_cases fb : FixedAt W b
    · obtain ⟨u,hu⟩:=fa
      obtain ⟨v,hv⟩:=fb
      have ca : FixedAt W a:=⟨u,hu⟩
      have cb : FixedAt W b:=⟨v,hv⟩
      have out : FixedAt W o:=⟨g.op.eval [u,v],fun x=>by simp [evaluate x,inputs,hu,hv]⟩
      simp [inputsFixed,inputs,ca,cb,out,budget,ab,Finset.filter_insert,singleton]
    · by_cases c : FixedAt W o <;> simp [inputsFixed,inputs,fa,fb,budget,Finset.filter_insert,singleton,c]
    · by_cases c : FixedAt W o <;> simp [inputsFixed,inputs,fa,fb,budget,Finset.filter_insert,singleton,c]
    · simp [inputsFixed,inputs,fa,fb,Finset.filter_insert,singleton]

theorem cancelConstants {X : Type} (N : Nat) (C : Circuit) (W : X→Nat→Bool)
    (shape : ∀g∈C.gates, Good False g)
    (evaluate : ∀j<C.size,∀x,W x (N+j)=(gateAt C j).op.eval ((gateAt C j).inputs.map (W x)))
    (A : Finset Nat) (raw : ∀i∈A,i<N)
    (seen : ∀i∈A,FixedAt W i ∧ ∃j<C.size,i∈(gateAt C j).inputs)
    (live : ∀j<C.size, FixedAt W (N+j) → ∃k<C.size,N+j∈(gateAt C k).inputs) :
    A.card + remaining bin C (eliminated N C W) C.size ≤ listed bin C.gates := by
  classical
  let I:=Finset.range C.size
  let T:=I.filter (fun j=>FixedAt W (N+j))
  let B:=T.image (fun j=>N+j)
  let F:=eliminated N C W
  let pieces:=fun j=>inputsFixed W (gateAt C j)
  have source {w} (h : FixedAt W w) (use : ∃j<C.size,w∈(gateAt C j).inputs) : w∈I.biUnion pieces := by
    obtain ⟨j,less,pin⟩:=use
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_range.mpr less,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr pin,h⟩⟩
  have sub : A∪B⊆I.biUnion pieces := by
    intro w hw
    rcases Finset.mem_union.mp hw with ha|hb
    · exact source (seen _ ha).1 (seen _ ha).2
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hb
      obtain ⟨idx,fixed⟩:=Finset.mem_filter.mp hj
      exact source fixed (live j (Finset.mem_range.mp idx) fixed)
  have dis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i hi h
    obtain ⟨j,_,wire⟩:=Finset.mem_image.mp h
    have below:=raw i hi;change N+j=i at wire;omega
  have first:=(Finset.card_le_card sub).trans (Finset.card_biUnion_le)
  have inj : Function.Injective (fun j : Nat=>N+j):=fun _ _ e=>Nat.add_left_cancel e
  rw [Finset.card_union_of_disjoint dis,show B.card=T.card from Finset.card_image_of_injective _ inj] at first
  let dropped:=fun j=>if j∈F then bin (gateAt C j).op else 0
  have charge (j) (hj : j∈I) : (pieces j).card ≤ (if FixedAt W (N+j) then 1 else 0)+dropped j := by
    have idx:=Finset.mem_range.mp hj
    have eqg : gateAt C j=C.gates[j] := List.getD_eq_getElem _ _ idx
    have good : Good False (gateAt C j):=eqg ▸ shape _ (List.getElem_mem idx)
    simpa [pieces,dropped,F,eliminated,idx] using countLocal W (gateAt C j) (N+j) good (evaluate j idx)
  have total:=Finset.sum_le_sum charge
  rw [Finset.sum_add_distrib,←show T.card=(∑j∈I,if FixedAt W (N+j) then 1 else 0) from Finset.card_filter _ _] at total
  have both : (∑j∈I,dropped j)+remaining bin C F C.size=listed bin C.gates := by
    rw [←full_price bin C]
    unfold remaining;rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _;by_cases mem : j∈F <;> simp [dropped,mem]
  change A.card+remaining bin C F C.size≤_
  omega
end PEqualNP.Outside.L_clb_127.X25689

namespace PEqualNP.Outside.L_clb_127.X25689
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical

theorem readFn {n : Nat} (x : Fin n → Bool) (i : Fin n) : (List.ofFn x).getD i.val false=x i := by
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]; simp

theorem rawReader {n : Nat} (C : Circuit) (back : ReadsBack n C) (s : Fin n)
    (out : C.output ≠ s.val) (x : Fin n→Bool)
    (diff : C.eval (List.ofFn (Function.update x s false)) ≠ C.eval (List.ofFn (Function.update x s true))) :
    ∃j<C.size,s.val∈(gateAt C j).inputs := by
  classical
  by_contra! absent
  let a:=List.ofFn (Function.update x s false)
  let b:=List.ofFn (Function.update x s true)
  have la : a.length=n:=List.length_ofFn
  have lb : b.length=n:=List.length_ofFn
  have same (w : Nat) (off : w≠s.val) : (run C.gates a).getD w false=(run C.gates b).getD w false := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases raw : w<n
      · let i : Fin n:=⟨w,raw⟩
        have ne : i≠s:=fun he=>off (congrArg Fin.val he)
        rw [run_input _ _ _ (by rwa [la]),run_input _ _ _ (by rwa [lb])]
        change (List.ofFn _).getD i.val false=(List.ofFn _).getD i.val false
        rw [readFn,readFn];simp [Function.update_of_ne ne]
      by_cases far : n+C.size≤w
      · rw [past C.gates a _ (by rwa [la]),past C.gates b _ (by rwa [lb])]
      let j:=w-n
      have add : n+j=w:=Nat.add_sub_of_le (by omega)
      have idx : j<C.size:=by dsimp [j];omega
      rw [←add,gv n C back a la j idx,gv n C back b lb j idx]
      congr 1
      apply List.map_congr_left
      intro v pin
      exact ih v (by have h:=back j idx v pin;omega) (fun h=>absent j idx (h ▸ pin))
  exact diff (same C.output out)

theorem initial {n : Nat} (C : Circuit) (fan : FanInTwo C)
    (f : (Fin n→Bool)→Bool) (rep : ∀x, C.eval (List.ofFn x)=f x)
    (nc : ¬∃b,∀x,f x=b) :
    ∃D : Circuit,(∀g∈D.gates,Good False g) ∧ ReadsBack n D ∧
      (∀p,listed p D.gates≤listed p C.gates) ∧ (∀x,D.eval (List.ofFn x)=f x) ∧
      ∀ i : Fin D.gates.length,n+i.val≠D.output → ∃ j : Fin D.gates.length,i<j ∧ reads (D.gates.get j) (n+i.val) := by
  obtain ⟨E,good,back,_,prices,value⟩:=engineWeighted False n n C (fun x : Fin n→Bool=>List.ofFn x) (fun x=>List.ofFn x)
    (fun _=>List.length_ofFn) (fun _=>List.length_ofFn) ∅ fan False.elim
    (fun w h=>Or.inr ⟨w,h,fun _=>rfl⟩) (fun ⟨b,v⟩=>nc ⟨b,fun x=>(rep x).symm.trans (v x)⟩) (by simp)
  obtain ⟨D,g,b,_,costs,eq,live⟩:=finishWeighted False n (fun x=>List.ofFn x) (fun _=>List.length_ofFn) f nc E
    good back (fun x=>(value x).trans (rep x))
  exact ⟨D,g,b,fun p=>(costs p).trans ((prices p).trans_eq (full_price p C)),eq,live⟩

theorem costs (C : Circuit) : listed inv C.gates=(C.gates.filter (fun g=>decide (g.op=GateOp.not))).length ∧
    listed bin C.gates=C.size-(C.gates.filter (fun g=>decide (g.op=GateOp.not))).length := by
  have h (gs : List Gate) : listed inv gs=(gs.filter (fun g=>decide (g.op=GateOp.not))).length ∧
      listed inv gs+listed bin gs=gs.length := by
    induction gs with
    | nil => simp [listed]
    | cons g gs ih =>
      by_cases yes : g.op=GateOp.not <;> simp [listed,inv,bin,yes] at ih ⊢ <;> omega
  obtain ⟨e,s⟩:=h C.gates
  exact ⟨e,by change _=C.gates.length-_;omega⟩
noncomputable def plug {n k : Nat} (wire : Fin k→Fin n) (fixed : Fin n→Bool) (y : Fin k→Bool) (i : Fin n) :=
  if i∈Finset.univ.image wire then decide (∃j,wire j=i ∧ y j=true) else fixed i

theorem onWire {n k : Nat} (wire : Fin k→Fin n) (fixed : Fin n→Bool) (inj : Function.Injective wire)
    (y : Fin k→Bool) (j : Fin k) : plug wire fixed y (wire j)=y j := by
  have inside : wire j∈Finset.univ.image wire:=Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
  have eq : (∃z,wire z=wire j ∧ y z=true) ↔ y j=true := by
    constructor
    · rintro ⟨z,h,v⟩;exact inj h ▸ v
    · exact fun v=>⟨j,rfl,v⟩
  simp [plug,inside,eq]

theorem restrict {n k : Nat} (C : Circuit) (fan : FanInTwo C) (wire : Fin k→Fin n) (fixed : Fin n→Bool)
    (inj : Function.Injective wire) (f : (Fin n→Bool)→Bool) (rep : ∀x,C.eval (List.ofFn x)=f x)
    (varies : ∃a b,f (plug wire fixed a)≠f (plug wire fixed b)) :
    ∃D : Circuit,FanInTwo D ∧ listed bin D.gates+
      ((Finset.univ : Finset (Fin n)).filter (fun i=>∃x,f (Function.update x i false)≠f (Function.update x i true))).card≤
      listed bin C.gates+k ∧ listed inv D.gates≤listed inv C.gates ∧ ∀y,D.eval (List.ofFn y)=f (plug wire fixed y) := by
  classical
  obtain ⟨a,b,diff⟩:=varies
  have nc : ¬∃v,∀x,f x=v := fun ⟨v,h⟩=>diff ((h _).trans (h _).symm)
  obtain ⟨E,good,back,prices,ef,live⟩:=initial C fan f rep nc
  let X:=Fin k→Bool
  let src : X→List Bool:=fun y=>List.ofFn (plug wire fixed y)
  let W:=fun (y : X) w=>(run E.gates (src y)).getD w false
  have val (j : Nat) (idx : j<E.size) (y : X) : W y (n+j)=(gateAt E j).op.eval ((gateAt E j).inputs.map (W y)):=
    gv n E back (src y) List.length_ofFn j idx
  have out (y : X) : W y E.output=f (plug wire fixed y):=ef _
  have varying : ¬FixedAt W E.output := fun ⟨v,c⟩=>diff ((out a).symm.trans ((c a).trans ((c b).symm.trans (out b))))
  let image:=Finset.univ.image wire
  let ess:=(Finset.univ : Finset (Fin n)).filter (fun i=>∃x,f (Function.update x i false)≠f (Function.update x i true))
  let miss:=ess\image
  let A:=miss.image Fin.val
  have low (w) (hw : w∈A) : w<n := by obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hw;exact i.isLt
  have gateGood j (h : j<E.size) : Good False (gateAt E j) := by
    rw [show gateAt E j=E.gates[j] from List.getD_eq_getElem _ _ h];exact good _ (List.getElem_mem h)
  have rawValue (i : Fin n) (y : X) : W y i.val=plug wire fixed y i := by
    unfold W; rw [run_input _ _ _ (by simpa [src] using i.isLt)];exact readFn _ _
  have seen (w) (hw : w∈A) : FixedAt W w ∧ ∃j<E.size,w∈(gateAt E j).inputs := by
    obtain ⟨i,mem,rfl⟩:=Finset.mem_image.mp hw
    obtain ⟨active,off⟩:=Finset.mem_sdiff.mp mem
    have c : FixedAt W i.val:=⟨fixed i,fun y=>by rw [rawValue];exact if_neg off⟩
    have ne : E.output≠i.val:=fun eq=>varying (eq ▸ c)
    obtain ⟨x,hx⟩:=(Finset.mem_filter.mp active).2
    exact ⟨c,rawReader E back i ne x (by simpa only [ef] using hx)⟩
  have used (j) (idx : j<E.size) (fix : FixedAt W (n+j)) : ∃l<E.size,n+j∈(gateAt E l).inputs := by
    have ne : n+j≠E.output:=fun eq=>varying (eq ▸ fix)
    obtain ⟨l,_,read⟩:=live ⟨j,idx⟩ ne
    have e : E.gates.get l=gateAt E l.val:=(List.getD_eq_getElem _ _ l.isLt).symm
    rw [e] at read
    exact ⟨l.val,l.isLt,(good_read (gateGood _ l.isLt) _).mp read⟩
  let F:=eliminated n E W
  have charged:=cancelConstants n E W good val A low seen used
  have mark (j) (hj : j∈F) : j<E.gates.length ∧ collapses W (n+j) (fun x=>W x (n+j)) := by
    obtain ⟨idx,why⟩:=Finset.mem_filter.mp hj
    have h:=Finset.mem_range.mp idx
    refine ⟨h,?_⟩
    rcases why with c|⟨w,mem,v,z⟩
    · exact Or.inl c
    · let g:=gateAt E j
      have shape:=gateGood j h
      have fanE:=good_fan good
      have belongs : g∈E.gates:=by rw [show g=E.gates[j] from List.getD_eq_getElem _ _ h];exact List.getElem_mem _
      have ops : g.op=.and ∨ g.op=.or ∨ g.op=.not := by rcases shape.1 with ⟨op,_⟩|⟨op,_⟩ <;> tauto
      have fold:=when_read W g (n+j) w v ops (fanE g belongs).2 (back j h) ((good_read shape w).mpr mem) z
      simpa only [val j h] using fold
  have inputs (w : Nat) (h : w<n) : (∃v,∀y,(src y).getD w false=v) ∨ ∃t,t<k ∧ ∀y,(src y).getD w false=(List.ofFn y).getD t false := by
    let i : Fin n:=⟨w,h⟩
    by_cases mem : i∈image
    · obtain ⟨j,_,e⟩:=Finset.mem_image.mp mem
      exact Or.inr ⟨j.val,j.isLt,fun y=>(readFn _ i).trans (e ▸ (onWire wire fixed inj y j).trans (readFn y j).symm)⟩
    · exact Or.inl ⟨fixed i,fun y=>(readFn _ i).trans (if_neg mem)⟩
  obtain ⟨D,dgood,_,_,dcost,deval⟩:=engineWeighted False n k E src (fun y=>List.ofFn y)
    (fun _=>List.length_ofFn) (fun _=>List.length_ofFn) F (good_fan good) False.elim inputs
    (fun ⟨v,h⟩=>varying ⟨v,h⟩) mark
  have cov : ess⊆miss∪image := by
    intro i hi;by_cases mem : i∈image
    · exact Finset.mem_union_right _ mem
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi,mem⟩)
  have many:=(Finset.card_le_card cov).trans (Finset.card_union_le _ _)
  have im : image.card=k:=by simp [image,Finset.card_image_of_injective _ inj]
  have am : A.card=miss.card:=Finset.card_image_of_injective _ Fin.val_injective
  have saved:=dcost bin
  change A.card+remaining bin E F E.size≤listed bin E.gates at charged
  have ib := prices bin
  have inversion : remaining inv E F E.size≤listed inv E.gates := by
    rw [←full_price inv E];unfold remaining;apply Finset.sum_le_sum
    intro j _;by_cases mem : j∈F <;> simp [mem]
  exact ⟨D,good_fan dgood,by change listed bin D.gates+ess.card≤_;omega,
    (dcost inv).trans (inversion.trans (prices inv)),fun y=>(deval y).trans (ef _)⟩
end PEqualNP.Outside.L_clb_127.X25689

namespace PEqualNP.Outside.L_clb_127.X25689.OldParity
open PEqualNP PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 5 * 2 ^ k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = f (fun i : Fin k => w.getD i false) := by
  induction k with
  | zero =>
    intro f m _
    refine ⟨[⟨if f (fun i => i.elim0) = true then GateOp.and else GateOp.or, []⟩], m, ?_, by simp,
      by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      by_cases h : f (fun i => i.elim0) = true <;> simp [h]
    · intro w hw
      have hf : (fun i : Fin 0 => w.getD i false) = (fun i => i.elim0) := Subsingleton.elim _ _
      rw [hf]
      by_cases h : f (fun i => i.elim0) = true <;>
        simp [wiresFrom, h, ← hw, GateOp.eval]
  | succ k ih =>
    intro f m hm
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega)
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [M, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have e0 : w2.getD o0 false = f (Fin.snoc (fun i : Fin k => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw
      have e1 : w2.getD o1 false = f (Fin.snoc (fun i : Fin k => w.getD i false) true) := by
        rw [ev1 w1 l1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD k false = w.getD k false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + 1) => w.getD i false)
          = Fin.snoc (fun i : Fin k => w.getD i false) (w.getD k false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 k o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD k false <;> simp

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

open PEqualNP.CircuitLowerBounds

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

open PEqualNP.CircuitLowerBounds

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Stat.const false) ≠ Stat.const c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Stat.const false) = Stat.const b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Stat.const false)
      = Stat.const b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      ((elim n gs (initStats n b, [])).1.getD C.output (Stat.const false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) ≠ Stat.const c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) with
  | const c => exact absurd hst (hout b c)
  | wire j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

def par (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)

theorem par_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.snoc y b) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  generalize (∑ i : Fin n, if y i = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]

theorem par_lower : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s →
      2 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    have hdep : ∃ x : Fin (n + 1 + 1) → Bool,
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c)
          (Function.update x (Fin.last (n + 1)) (!x (Fin.last (n + 1))))
        ≠ (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) x := by
      refine ⟨Fin.snoc (fun _ => false) false, ?_⟩
      simp only [Fin.snoc_last, Fin.update_snoc_last, par_snoc]
      simp
    have hnc : ∀ b : Bool, ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y b)
        ≠ (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y' b) := by
      intro b
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    obtain ⟨b, s', hs, h'⟩ := gate_elim_two (n + 1) _ s hdep hnc h
    have e : (fun y : Fin (n + 1) → Bool =>
          (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y b))
        = fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) (xor b c) := by
      funext y
      show xor (par (n + 1 + 1) (Fin.snoc y b)) c = _
      rw [par_snoc]
      cases par (n + 1) y <;> cases b <;> cases c <;> rfl
    rw [e] at h'
    have := ih _ _ h'
    omega

theorem parity_lower : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    2 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have := par_lower n false s h'
    omega

open PEqualNP.CircuitLowerBounds

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

def statAt (n : ℕ) (i : Fin (n + 1)) (b : Bool) : List Stat :=
  List.ofFn (Fin.insertNth i (Stat.const b) (fun k : Fin n => Stat.wire k) : Fin (n + 1) → Stat)

theorem statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length = n + 1 := by
  simp [statAt]

theorem statAt_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (statAt n i b).getD i (Stat.const false) = Stat.const b := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_same]

theorem statAt_above (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    (statAt n i b).getD (i.succAbove k) (Stat.const false) = Stat.wire k := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_succAbove]

theorem inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool))
      (statAt n i b, []) := by
  refine ⟨by simp [statAt], ?_⟩
  have key : ∀ j : Fin (n + 1),
      ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · rw [statAt_at, getD_ofFn, Fin.insertNth_apply_same]
      exact ⟨trivial, rfl⟩
    · rw [statAt_above, getD_ofFn, Fin.insertNth_apply_succAbove]
      refine ⟨?_, ?_⟩
      · show (k : ℕ) < n + 0
        have := k.isLt
        omega
      · show (List.ofFn y).getD k false = y k
        exact getD_ofFn n y false k
  intro j
  by_cases hlt : j < n + 1
  · exact key ⟨j, hlt⟩
  · show ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
    rw [List.getD_eq_default _ _ (by rw [statAt_length]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

def stF (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Stat :=
  (elim n gs (statAt n i b, [])).1.getD a (Stat.const false)

theorem stF_self (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b i = Stat.const b := by
  show (elim n gs (statAt n i b, [])).1.getD i (Stat.const false) = _
  rw [elim_getD n i _ gs _ (by
    show (i : ℕ) < (statAt n i b).length
    rw [statAt_length]; exact i.isLt)]
  exact statAt_at n i b

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

theorem elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]

theorem elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)

theorem const_of_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Stat.const false) = Stat.const c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc
  obtain ⟨c, hc'⟩ := elimStep_const n (elim n pre acc) g hg a ha hc
  refine ⟨c, ?_⟩
  rw [elim_split_getD n pre g post acc _ _ (le_refl _)]
  rw [elim_fst_len] at hc'
  exact hc'

theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Stat.const false) = Stat.const c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Stat.const false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega

theorem supp_B (m : ℕ) (i : Fin m) (B : ℕ → Prop) (hi : B i) : ∀ gs : List Gate,
    (∀ p g, gs[p]? = some g → ¬ B (m + p) → ∀ a ∈ g.inputs, ¬ B a) →
    ∀ j, ¬ B j → i ∉ (suppsFrom gs (inputSupps m)).getD j ∅ := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ j hj
    show i ∉ (inputSupps m).getD j ∅
    by_cases hlt : j < m
    · rw [inputSupps_getD m j hlt, Finset.mem_singleton]
      intro e
      apply hj
      have e' : (i : ℕ) = j := congrArg Fin.val e
      rw [← e']; exact hi
    · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp
  | append_singleton gs g ih =>
    intro h j hj
    have ih' := ih (fun p g' hp => h p g' (by
      obtain ⟨hpl, _⟩ := List.getElem?_eq_some_iff.1 hp
      rw [List.getElem?_append_left hpl]; exact hp))
    have hs : suppsFrom (gs ++ [g]) (inputSupps m) = suppsFrom gs (inputSupps m)
        ++ [gateSupp (suppsFrom gs (inputSupps m)) g] := by
      rw [suppsFrom_append]; rfl
    have hl : (suppsFrom gs (inputSupps m)).length = m + gs.length := by
      rw [length_suppsFrom]; simp [inputSupps]
    rw [hs]
    by_cases hjl : j = m + gs.length
    · subst hjl
      rw [getD_snoc_len _ _ _ _ hl]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp _ g _).1 hmem
      exact ih' a (h gs.length g List.getElem?_concat_length hj a ha) hia
    · rw [getD_snoc_ne _ _ _ _ (by rw [hl]; exact hjl)]
      exact ih' j hj

theorem exists_reader (m : ℕ) (i : Fin m) (B : ℕ → Prop) (hi : B i) (gs : List Gate) (o : ℕ)
    (ho : ¬ B o) (hdep : i ∈ (suppsFrom gs (inputSupps m)).getD o ∅) :
    ∃ p g, gs[p]? = some g ∧ ¬ B (m + p) ∧ ∃ a ∈ g.inputs, B a := by
  by_contra hno
  exact supp_B m i B hi gs
    (fun p g hp hB a ha hBa => hno ⟨p, g, hp, hB, a, ha, hBa⟩) o ho hdep

theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj

def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, ∃ c, stF n gs i b a = Stat.const c

theorem three_count (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) {p1, p2, p3} (by
    intro p hp
    have hR : RC n gs i b p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> assumption
    obtain ⟨g, hg, a, ha, c, hc⟩ := hR
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  have hcard : ({p1, p2, p3} : Finset ℕ).card = 3 :=
    Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩
  rw [hcard] at hcount
  simpa using hcount

theorem three_core (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (o : ℕ)
    (hsupp : ∀ i : Fin (n + 1), i ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ (i : Fin (n + 1)) (b c : Bool), stF n gs i b o ≠ Stat.const c)
    (g0 : Gate) (h0 : gs[0]? = some g0) (i : Fin (n + 1)) (hi0 : (i : ℕ) ∈ g0.inputs)
    (halt : (∀ c, ∃ b, stF n gs i b (n + 1) = Stat.const c) ∨
      ∃ p' g', p' ≠ 0 ∧ gs[p']? = some g' ∧ (i : ℕ) ∈ g'.inputs) :
    ∃ b, (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hnok := clean_nok _ gs hcl
  have hxi : ∀ b, stF n gs i b i = Stat.const b := stF_self n gs i
  have hrd : ∀ (b : Bool) (p : ℕ) (g : Gate) (a : ℕ), gs[p]? = some g → a ∈ g.inputs →
      stF n gs i b a = Stat.const (fixBit g) → ∃ c, stF n gs i b (n + 1 + p) = Stat.const c := by
    intro b p g a hp ha hc
    have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
    have := const_of_read n gs (statAt n i b, []) p g hp (hnok g (List.mem_of_getElem? hp)) a ha
      (by rw [hL]; exact (hcl p g hp).lt a ha) hc
    rw [hL] at this
    exact this
  have hg0c : ∃ c0, stF n gs i (fixBit g0) (n + 1) = Stat.const c0 :=
    hrd (fixBit g0) 0 g0 i h0 hi0 (hxi _)
  have hox : o ≠ i := fun e => hout i false false (by rw [e]; exact hxi false)
  have ho0 : o ≠ n + 1 := by
    intro e
    obtain ⟨c0, h⟩ := hg0c
    exact hout i (fixBit g0) c0 (by rw [e]; exact h)
  have R0 : ∀ b, RC n gs i b 0 := fun b => ⟨g0, h0, i, hi0, b, hxi b⟩
  obtain ⟨p, g2, hp, hBp, a, ha, hBa⟩ := exists_reader (n + 1) i
    (fun a => a = i ∨ a = n + 1) (Or.inl rfl) gs o
    (fun h => h.elim hox ho0) (hsupp i)
  have hp0 : p ≠ 0 := fun e => hBp (Or.inr (by omega))
  have ha2 : ∃ c, stF n gs i (fixBit g0) a = Stat.const c := by
    rcases hBa with h | h
    · exact ⟨fixBit g0, by rw [h]; exact hxi _⟩
    · rw [h]; exact hg0c

  have third : ∀ (b c2 : Bool), stF n gs i b (n + 1 + p) = Stat.const c2 →
      ∃ p3 g3, gs[p3]? = some g3 ∧ p3 ≠ 0 ∧ p3 ≠ p ∧
        ∃ a3 ∈ g3.inputs, a3 = (i : ℕ) ∨ a3 = n + 1 ∨ a3 = n + 1 + p := by
    intro b c2 hc2
    obtain ⟨p3, g3, hp3, hB3, a3, ha3, hBa3⟩ := exists_reader (n + 1) i
      (fun a => a = i ∨ a = n + 1 ∨ a = n + 1 + p) (Or.inl rfl) gs o
      (fun h => by
        rcases h with h | h | h
        · exact hox h
        · exact ho0 h
        · exact hout i b c2 (by rw [h]; exact hc2)) (hsupp i)
    exact ⟨p3, g3, hp3, fun e => hB3 (Or.inr (Or.inl (by omega))),
      fun e => hB3 (Or.inr (Or.inr (by omega))), a3, ha3, hBa3⟩
  by_cases hc2 : ∃ c, stF n gs i (fixBit g0) (n + 1 + p) = Stat.const c
  · obtain ⟨c2, hc2⟩ := hc2
    obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third (fixBit g0) c2 hc2
    refine ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
      (Ne.symm h3p) (R0 _) ⟨g2, hp, a, ha, ha2⟩ ⟨g3, hp3, a3, ha3, ?_⟩⟩
    rcases hBa3 with h | h | h
    · exact ⟨fixBit g0, by rw [h]; exact hxi _⟩
    · rw [h]; exact hg0c
    · exact ⟨c2, by rw [h]; exact hc2⟩
  · by_cases hx : (i : ℕ) ∈ g2.inputs
    · obtain ⟨c2, hc2'⟩ := hrd (fixBit g2) p g2 i hp hx (hxi _)
      obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third (fixBit g2) c2 hc2'
      rcases hBa3 with h | h | h
      · exact ⟨fixBit g2, three_count n gs hcl i (fixBit g2) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, i, hx, _, hxi _⟩
          ⟨g3, hp3, a3, ha3, fixBit g2, by rw [h]; exact hxi _⟩⟩
      · exact ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, a, ha, ha2⟩
          ⟨g3, hp3, a3, ha3, by rw [h]; exact hg0c⟩⟩
      · exact ⟨fixBit g2, three_count n gs hcl i (fixBit g2) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, i, hx, _, hxi _⟩
          ⟨g3, hp3, a3, ha3, c2, by rw [h]; exact hc2'⟩⟩
    · have ha' : a = n + 1 := by
        rcases hBa with h | h
        · exact absurd (h ▸ ha) hx
        · exact h
      rw [ha'] at ha
      rcases halt with hG | ⟨p', g', hp'0, hp', hx'⟩
      · obtain ⟨b, hb⟩ := hG (fixBit g2)
        obtain ⟨c2, hc2'⟩ := hrd b p g2 (n + 1) hp ha hb
        obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third b c2 hc2'
        refine ⟨b, three_count n gs hcl i b 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, n + 1, ha, _, hb⟩ ⟨g3, hp3, a3, ha3, ?_⟩⟩
        rcases hBa3 with h | h | h
        · exact ⟨b, by rw [h]; exact hxi _⟩
        · exact ⟨fixBit g2, by rw [h]; exact hb⟩
        · exact ⟨c2, by rw [h]; exact hc2'⟩
      · have hpp : p ≠ p' := by
          intro e
          rw [← e, hp] at hp'
          exact hx (Option.some.inj hp' ▸ hx')
        exact ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p' (Ne.symm hp0)
          (Ne.symm hp'0) hpp (R0 _) ⟨g2, hp, n + 1, ha, hg0c⟩
          ⟨g', hp', i, hx', _, hxi _⟩⟩

theorem stat_first (n : ℕ) (gs : List Gate) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b (n + 1) = (simplify g0.op n
      (g0.inputs.map fun a => (statAt n i b).getD a (Stat.const false))).2 := by
  obtain ⟨pre, post, rfl, hpre⟩ := split_at gs 0 g0 h0
  have hnil : pre = [] := List.eq_nil_of_length_eq_zero hpre
  subst hnil
  show (elim n ([] ++ g0 :: post) (statAt n i b, [])).1.getD (n + 1) (Stat.const false) = _
  rw [elim_split_getD n [] g0 post _ (n + 1) _ (by
    show n + 1 ≤ (statAt n i b).length + 0
    rw [statAt_length])]
  exact getD_snoc_len (statAt n i b) _ _ _ (statAt_length n i b)

theorem first_any (n : ℕ) (gs : List Gate) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i : Fin (n + 1))
    (hshape : (g0.op = GateOp.not ∧ g0.inputs = [(i : ℕ)]) ∨
      ((g0.op = GateOp.and ∨ g0.op = GateOp.or) ∧ g0.inputs = [(i : ℕ), (i : ℕ)])) :
    ∀ c, ∃ b, stF n gs i b (n + 1) = Stat.const c := by
  intro c
  rcases hshape with ⟨hop, hin⟩ | ⟨hop | hop, hin⟩
  · refine ⟨!c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpNot]
  · refine ⟨c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpAnd]
  · refine ⟨c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpOr]

theorem single_reader (n : ℕ) (gs : List Gate) (o : ℕ) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i k : Fin (n + 1)) (hik : k ≠ i) (hop : g0.op = GateOp.and ∨ g0.op = GateOp.or)
    (hin : g0.inputs = [(i : ℕ), (k : ℕ)]) (hoi : o ≠ i)
    (hno : ∀ p' g', gs[p']? = some g' → p' ≠ 0 → (i : ℕ) ∉ g'.inputs)
    (hdep : ∀ u : Fin (n + 1) → Bool,
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false) : False := by
  obtain ⟨pre, post, rfl, hpre⟩ := split_at gs 0 g0 h0
  have hnil : pre = [] := List.eq_nil_of_length_eq_zero hpre
  subst hnil
  have hno' : ∀ g ∈ post, (i : ℕ) ∉ g.inputs := by
    intro g hg
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno (q + 1) g (by simpa using hq) (by omega)
  let u : Fin (n + 1) → Bool := fun j => if j = k then fixBit g0 else false
  have huk : u k = fixBit g0 := by simp [u]
  have hu'k : Function.update u i (!u i) k = fixBit g0 := by
    rw [Function.update_of_ne hik]; exact huk
  apply hdep u
  show (wiresFrom post (List.ofFn (Function.update u i (!u i)) ++
      [g0.op.eval (g0.inputs.map fun a => (List.ofFn (Function.update u i (!u i))).getD a false)])).getD
        o false
    = (wiresFrom post (List.ofFn u ++
      [g0.op.eval (g0.inputs.map fun a => (List.ofFn u).getD a false)])).getD o false
  apply agree_except i post _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjl : j = n + 1
  · rw [hjl, getD_snoc_len _ _ _ _ (by simp), getD_snoc_len _ _ _ _ (by simp), hin]
    simp only [List.map_cons, List.map_nil, getD_ofFn, huk, hu'k]
    rcases hop with hop | hop
    · have hf : fixBit g0 = false := by simp [fixBit, hop]
      rw [hop, hf]; simp [GateOp.eval]
    · have hf : fixBit g0 = true := by simp [fixBit, hop]
      rw [hop, hf]; simp [GateOp.eval]
  · rw [getD_snoc_ne _ _ _ _ (by simpa using hjl), getD_snoc_ne _ _ _ _ (by simpa using hjl)]
    by_cases hlt : j < n + 1
    · have e1 : (List.ofFn (Function.update u i (!u i))).getD j false
          = Function.update u i (!u i) ⟨j, hlt⟩ := getD_ofFn (n + 1) _ false ⟨j, hlt⟩
      have e2 : (List.ofFn u).getD j false = u ⟨j, hlt⟩ := getD_ofFn (n + 1) _ false ⟨j, hlt⟩
      rw [e1, e2]
      exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem three_saved (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (o : ℕ)
    (hdep : ∀ (i : Fin (n + 1)) (u : Fin (n + 1) → Bool),
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false)
    (hout : ∀ (i : Fin (n + 1)) (b c : Bool), stF n gs i b o ≠ Stat.const c) :
    ∃ (i : Fin (n + 1)) (b : Bool),
      (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hsupp : ∀ i : Fin (n + 1), i ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅ := by
    intro i
    by_contra hns
    refine hdep i (fun _ => false) ?_
    exact (agree_wiresFrom (Function.update (fun _ => false) i (!false)) (fun _ => false) gs _ _ _
      (agree_inputs _ _)).2.2 o (by
        intro k hk
        have : k ≠ i := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
  have hoi : ∀ i : Fin (n + 1), o ≠ i :=
    fun i e => hout i false false (by rw [e]; exact stF_self n gs i false)
  have hg0 : ∃ g0, gs[0]? = some g0 := by
    cases gs with
    | nil =>
      exfalso
      obtain ⟨p, g, hp, _⟩ := exists_reader (n + 1) 0 (fun a => a = ((0 : Fin (n + 1)) : ℕ)) rfl
        [] o (hoi 0) (hsupp 0)
      simp at hp
    | cons g _ => exact ⟨g, rfl⟩
  obtain ⟨g0, h0⟩ := hg0
  rcases hcl 0 g0 h0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
      (by rw [hin]; exact List.mem_cons_self)
      (Or.inl (first_any n gs g0 h0 ⟨j, hj⟩ (Or.inl ⟨hop, hin⟩)))
    exact ⟨⟨j, hj⟩, b, hb⟩
  · by_cases hjk : j = k
    · subst hjk
      obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
        (by rw [hin]; exact List.mem_cons_self)
        (Or.inl (first_any n gs g0 h0 ⟨j, hj⟩ (Or.inr ⟨hop, hin⟩)))
      exact ⟨⟨j, hj⟩, b, hb⟩
    · by_cases hr : ∃ p' g', p' ≠ 0 ∧ gs[p']? = some g' ∧ j ∈ g'.inputs
      · obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
          (by rw [hin]; exact List.mem_cons_self) (Or.inr hr)
        exact ⟨⟨j, hj⟩, b, hb⟩
      · exfalso
        exact single_reader n gs o g0 h0 ⟨j, hj⟩ ⟨k, hk⟩
          (fun e => hjk (congrArg Fin.val e).symm) hop hin (hoi ⟨j, hj⟩)
          (fun p' g' hp' hp0 hx => hr ⟨p', g', hp0, hp', hx⟩) (hdep ⟨j, hj⟩)

theorem par_insertNth (n : ℕ) (i : Fin (n + 1)) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.insertNth i b y : Fin (n + 1) → Bool) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  generalize (∑ k : Fin n, if y k = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]

theorem par_flip (n : ℕ) (i : Fin (n + 1)) (u : Fin (n + 1) → Bool) :
    par (n + 1) (Function.update u i (!u i)) = !par (n + 1) u := by
  have key : ∀ (x : Bool) (p : Fin n → Bool),
      par (n + 1) (Function.update (Fin.insertNth i x p : Fin (n + 1) → Bool) i (!x))
        = !par (n + 1) (Fin.insertNth i x p : Fin (n + 1) → Bool) := by
    intro x p
    rw [Fin.update_insertNth, par_insertNth, par_insertNth]
    cases par n p <;> cases x <;> rfl
  have := key (u i) (Fin.removeNth i u)
  rw [Fin.insertNth_self_removeNth] at this
  exact this

theorem clean_step (n : ℕ) (c : Bool) (s : ℕ)
    (h : HasClean (n + 1 + 1) (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) s) :
    ∃ (c' : Bool) (s' : ℕ), s' + 3 ≤ s ∧
      HasClean (n + 1) (fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) c') s' := by
  obtain ⟨gs, o, hcl, hsz, hev⟩ := h
  have hev' : ∀ x : Fin (n + 1 + 1) → Bool,
      (wiresFrom gs (List.ofFn x)).getD o false = xor (par (n + 1 + 1) x) c := hev
  have hok : ∀ g ∈ gs, Ok g := fun g hg => (clean_nok _ gs hcl g hg).1
  have hinv : ∀ (i : Fin (n + 1 + 1)) (b : Bool) (y : Fin (n + 1) → Bool),
      Inv (n + 1) (List.ofFn y)
        (wiresFrom gs (List.ofFn (Fin.insertNth i b y : Fin (n + 1 + 1) → Bool)))
        (elim (n + 1) gs (statAt (n + 1) i b, [])) :=
    fun i b y => inv_elim (n + 1) _ (by simp) gs _ _ hok (inv_at (n + 1) i b y)
  have hval : ∀ (i : Fin (n + 1 + 1)) (b : Bool) (y : Fin (n + 1) → Bool),
      (stF (n + 1) gs i b o).val (wiresFrom (elim (n + 1) gs (statAt (n + 1) i b, [])).2
        (List.ofFn y)) = xor (par (n + 1) y) (xor b c) := by
    intro i b y
    have := ((hinv i b y).2 o).2
    rw [hev', par_insertNth, Bool.xor_assoc] at this
    exact this
  have hout : ∀ (i : Fin (n + 1 + 1)) (b c' : Bool), stF (n + 1) gs i b o ≠ Stat.const c' := by
    intro i b c' hst
    have h1 := hval i b (Fin.snoc (fun _ => false) false)
    have h2 := hval i b (Fin.snoc (fun _ => false) true)
    rw [hst] at h1 h2
    have e := h1.symm.trans h2
    rw [par_snoc, par_snoc] at e
    revert e
    cases par n (fun _ => false) <;> cases b <;> cases c <;> simp
  have hdep : ∀ (i : Fin (n + 1 + 1)) (u : Fin (n + 1 + 1) → Bool),
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false := by
    intro i u
    rw [hev', hev', par_flip]
    cases par (n + 1 + 1) u <;> cases c <;> simp
  obtain ⟨i, b, hb⟩ := three_saved (n + 1) gs hcl o hdep hout
  cases hst : stF (n + 1) gs i b o with
  | const c' => exact absurd hst (hout i b c')
  | wire j =>
    refine ⟨xor b c, (elim (n + 1) gs (statAt (n + 1) i b, [])).2.length, by omega,
      (elim (n + 1) gs (statAt (n + 1) i b, [])).2, j, ?_, le_refl _, ?_⟩
    · exact clean_elim (n + 1) (List.ofFn fun _ : Fin (n + 1) => false) (by simp) gs _ _ hok
        (inv_at (n + 1) i b _) (by intro p g hp; simp at hp)
    · intro y
      have := hval i b y
      rw [hst] at this
      exact this

theorem par_lower3 : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasClean (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s → 3 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    obtain ⟨c', s', hs, h'⟩ := clean_step n c s h
    have := ih c' s' h'
    omega

theorem parity_lower3 : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    3 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have hnc : ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y
          ≠ (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y' := by
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    have := par_lower3 n false s (clean_of (n + 1) _ s hnc h')
    omega

open PEqualNP.CircuitLowerBounds

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

theorem vl_abs {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (w : ℕ)
    (hw : w ∈ g.inputs) (hv : vl gs u w = fixBit g) : vl gs u (k + p) = fixBit g := by
  rw [vl_gate gs hcl u p g hp]
  rcases hop with h | h
  · have hf : fixBit g = false := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).all id = false
    rw [List.all_eq_false]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩
  · have hf : fixBit g = true := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).any id = true
    rw [List.any_eq_true]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩

theorem agree_B {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool)
    (B : ℕ → Prop) (L : ℕ) (hin : ∀ j, j < k → ¬ B j → vl gs u j = vl gs u' j)
    (hstep : ∀ p g, gs[p]? = some g → k + p < L → ¬ B (k + p) → (∃ a ∈ g.inputs, B a) →
      (∀ j, j < k + p → ¬ B j → vl gs u j = vl gs u' j) → vl gs u (k + p) = vl gs u' (k + p)) :
    ∀ j, j < L → ¬ B j → vl gs u j = vl gs u' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjL hB
    by_cases hjk : j < k
    · exact hin j hjk hB
    · obtain ⟨p, rfl⟩ : ∃ p, j = k + p := ⟨j - k, by omega⟩
      cases hp : gs[p]? with
      | none =>
        have hlen : gs.length ≤ p := List.getElem?_eq_none_iff.1 hp
        have h1 : ∀ v : Fin k → Bool, vl gs v (k + p) = false := by
          intro v
          unfold vl
          exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
        rw [h1, h1]
      | some g =>
        by_cases hr : ∃ a ∈ g.inputs, B a
        · exact hstep p g hp hjL hB hr (fun j' hj' hB' => ih j' hj' (by omega) hB')
        · exact vl_congr gs hcl u u' p g hp (fun a ha =>
            ih a ((hcl p g hp).lt a ha) (by have := (hcl p g hp).lt a ha; omega)
              (fun hBa => hr ⟨a, ha, hBa⟩))

theorem takes {k : ℕ} (gs : List Gate)
    (hM1 : ∀ p g, gs[p]? = some g → ∀ c, ¬ ∀ u : Fin k → Bool, vl gs u (k + p) = c)
    (w : ℕ) (hw : w < k + gs.length) (c : Bool) : ∃ u : Fin k → Bool, vl gs u w = c := by
  by_cases hwk : w < k
  · exact ⟨fun _ => c, by rw [vl_input gs _ w hwk]⟩
  · obtain ⟨p, rfl⟩ : ∃ p, w = k + p := ⟨w - k, by omega⟩
    have hpl : p < gs.length := by omega
    by_contra hno
    apply hM1 p gs[p] (List.getElem?_eq_getElem hpl) (!c)
    intro u
    have h := fun h => hno ⟨u, h⟩
    revert h
    cases vl gs u (k + p) <;> cases c <;> simp

theorem gate_eq {gs : List Gate} {p q : ℕ} {g g' : Gate} (h : gs[p]? = some g)
    (h' : gs[q]? = some g') (e : p = q) : g = g' := by
  subst e
  rw [h] at h'
  exact Option.some.inj h'

theorem two_inputs {m : ℕ} {g : Gate} (hg : CleanGate m g) (a b w : ℕ) (ha : a ∈ g.inputs)
    (hb : b ∈ g.inputs) (hab : a ≠ b) (hw : w ∈ g.inputs) : w = a ∨ w = b := by
  rcases hg with ⟨_, j, _, hin⟩ | ⟨_, j, k, _, _, hin⟩ <;> rw [hin] at ha hb hw <;>
    simp at ha hb hw <;> omega

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨_, j, hc3, hlen, ?_⟩
    intro y
    have h := hval y
    rw [hst] at h
    exact h

theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Stat.const false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]

theorem drop_const (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (c : Bool)
    (hp : p < gs.length) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  exact drop_core k pre g post hcl o (Stat.const c) (fun y => ⟨trivial, (heq y).symm⟩) hnc

abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.insertNth i b y

def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
  (elim n gs (statAt n i b, [])).2

def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
  ∃ c, stF n gs i b a = Stat.const c

theorem inv_stF (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (y : Fin n → Bool) :
    Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b, [])) :=
  inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)

theorem st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j = Stat.const c) (y : Fin n → Bool) :
    vl gs (ins i b y) j = c := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.const c from h] at h1
  exact h1.symm

theorem st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j q : ℕ) (h : stF n gs i b j = Stat.wire q) (y : Fin n → Bool) :
    vl gs (ins i b y) j = vl (passG n gs i b) y q := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.wire q from h] at h1
  exact h1.symm

theorem st_other (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (X : Fin (n + 1))
    (h : X ≠ i) : ∃ k, k < n ∧ stF n gs i b X = Stat.wire k := by
  rcases Fin.eq_self_or_eq_succAbove i X with e | ⟨k, e⟩
  · exact absurd e h
  · refine ⟨k, k.isLt, ?_⟩
    rw [e]
    show (elim n gs (statAt n i b, [])).1.getD (i.succAbove k) (Stat.const false) = _
    rw [elim_getD n _ _ gs _ (by
      show ((i.succAbove k : Fin (n + 1)) : ℕ) < (statAt n i b).length
      rw [statAt_length]; exact (i.succAbove k).isLt)]
    exact statAt_above n i b k

theorem st_gate (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ t, stF n gs i b (n + 1 + p)
      = (simplify g.op (n + t) (g.inputs.map (stF n gs i b))).2 := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  refine ⟨(elim n pre (statAt n i b, [])).2.length, ?_⟩
  have e1 : stF n (pre ++ g :: post) i b (n + 1 + pre.length)
      = (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false) :=
    elim_split_getD n pre g post _ _ _ (by rw [hL])
  have e2 : (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false)
      = (simplify g.op (n + (elim n pre (statAt n i b, [])).2.length)
          (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))).2 :=
    getD_snoc_len _ _ _ _ (by rw [elim_fst_len, hL])
  have e3 : (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))
      = g.inputs.map (stF n (pre ++ g :: post) i b) :=
    List.map_congr_left (fun a ha =>
      (elim_split_getD_lt n pre g post _ a _ (by rw [hL]; exact hlt a ha)).symm)
  rw [e1, e2, e3]

theorem simp_allconst (op : GateOp) (t : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (h : ∀ s ∈ ins, ∃ c, s = Stat.const c) : ∃ c, (simplify op t ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩

theorem simp_fresh (g : Gate) (m : ℕ) (hg : CleanGate m g) (t : ℕ) (F : ℕ → Stat)
    (h : ∀ a ∈ g.inputs, ∀ c, F a ≠ Stat.const c) :
    (simplify g.op t (g.inputs.map F)).2 = Stat.wire t := by
  rcases hg with ⟨hop, j, _, hin⟩ | ⟨hop | hop, j, k, _, _, hin⟩
  · have h1 := h j (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q => simp [simplify, simpNot, hF]
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q =>
      cases hF' : F k with
      | const c => exact absurd hF' (h2 c)
      | wire q' => simp [simplify, simpAnd, hF, hF']
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q =>
      cases hF' : F k with
      | const c => exact absurd hF' (h2 c)
      | wire q' => simp [simplify, simpOr, hF, hF']

theorem st_allconst (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, IsC n gs i b a) : IsC n gs i b (n + 1 + p) := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  have hn := (hcl p g hp).nok
  obtain ⟨c, hc⟩ := simp_allconst g.op (n + t) (g.inputs.map (stF n gs i b)) hn.1.1
    (by simpa using hn.1.2) (by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
      exact h a ha)
  exact ⟨c, by rw [ht]; exact hc⟩

theorem st_fresh (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, ∀ c, stF n gs i b a ≠ Stat.const c) :
    ∃ q, n ≤ q ∧ stF n gs i b (n + 1 + p) = Stat.wire q := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  exact ⟨n + t, by omega, by rw [ht]; exact simp_fresh g _ (hcl p g hp) _ _ h⟩

theorem rc_of_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hc : IsC n gs i b (n + 1 + p)) :
    RC n gs i b p := by
  by_contra hno
  obtain ⟨q, _, hq⟩ := st_fresh n gs hcl i b p g hp
    (fun a ha c' hc' => hno ⟨g, hp, a, ha, c', hc'⟩)
  obtain ⟨c, hc⟩ := hc
  rw [hq] at hc
  cases hc

theorem const_read (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs)
    (hc : stF n gs i b a = Stat.const (fixBit g)) : IsC n gs i b (n + 1 + p) := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have h := const_of_read n gs (statAt n i b, []) p g hp ((hcl p g hp).nok) a ha
    (by rw [hL]; exact (hcl p g hp).lt a ha) hc
  rw [hL] at h
  exact h

theorem st_shape (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs) (c : Bool)
    (hc : stF n gs i b a = Stat.const c) (hn : ∀ c', stF n gs i b (n + 1 + p) ≠ Stat.const c') :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ c ≠ fixBit g ∧
      ∃ w ∈ g.inputs, ∀ c', stF n gs i b w ≠ Stat.const c' := by
  have hw : ∃ w ∈ g.inputs, ∀ c', stF n gs i b w ≠ Stat.const c' := by
    by_contra hno
    obtain ⟨c', hc'⟩ := st_allconst n gs hcl i b p g hp (fun a' ha' => by
      by_contra h'
      exact hno ⟨a', ha', fun c' hc' => h' ⟨c', hc'⟩⟩)
    exact hn c' hc'
  refine ⟨?_, ?_, hw⟩
  · rcases hcl p g hp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · exfalso
      obtain ⟨w, hw1, hw2⟩ := hw
      have e1 : w = j := by rw [hin] at hw1; simpa using hw1
      have e2 : a = j := by rw [hin] at ha; simpa using ha
      exact hw2 c (by rw [e1, ← e2]; exact hc)
    · exact hop
  · intro e
    obtain ⟨c', hc'⟩ := const_read n gs hcl i b p g hp a ha (by rw [← e]; exact hc)
    exact hn c' hc'

theorem four_count (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    (passG n gs i b).length + 4 ≤ gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) {p1, p2, p3, p4} (by
    intro p hp
    have hR : RC n gs i b p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨g, hg, a, ha, c, hc⟩ := hR
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rw [hcard] at hcount
  simpa [passG] using hcount

def Red (n : ℕ) (gs : List Gate) (o : ℕ) : Prop :=
  ∃ (i : Fin (n + 1)) (b : Bool) (gs' : List Gate) (o' : ℕ), CleanL n gs' ∧
    gs'.length + 4 ≤ gs.length ∧ ∀ y : Fin n → Bool, vl gs' y o' = vl gs (ins i b y) o

structure Min (n : ℕ) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL (n + 1) gs
  hdep : ∀ (i : Fin (n + 1)) (u : Fin (n + 1) → Bool),
    vl gs (Function.update u i (!u i)) o ≠ vl gs u o
  hnc : ∀ (i : Fin (n + 1)) (b : Bool), ∃ y y' : Fin n → Bool,
    vl gs (ins i b y) o ≠ vl gs (ins i b y') o
  m1 : ∀ p g, gs[p]? = some g → ∀ c, ¬ ∀ u : Fin (n + 1) → Bool, vl gs u (n + 1 + p) = c
  m2 : ∀ p g, gs[p]? = some g → ∀ j, j < n + 1 + p →
    ¬ ∀ u : Fin (n + 1) → Bool, vl gs u (n + 1 + p) = vl gs u j
  nored : ¬ Red n gs o

section

variable {n : ℕ} {gs : List Gate} {o : ℕ}

theorem Min.out (M : Min n gs o) (i : Fin (n + 1)) (b c : Bool) :
    stF n gs i b o ≠ Stat.const c := by
  intro h
  obtain ⟨y, y', hne⟩ := M.hnc i b
  exact hne ((st_val_const n gs M.hcl i b o c h y).trans
    (st_val_const n gs M.hcl i b o c h y').symm)

theorem Min.pass (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) :
    ∃ j, CleanL n (passG n gs i b) ∧
      ∀ y : Fin n → Bool, vl (passG n gs i b) y j = vl gs (ins i b y) o := by
  cases hst : stF n gs i b o with
  | const c => exact absurd hst (M.out i b c)
  | wire j =>
    refine ⟨j, ?_, fun y => (st_val_wire n gs M.hcl i b o j hst y).symm⟩
    exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
      (fun g hg => (clean_nok _ gs M.hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp)

theorem Min.nf4 (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2)
    (h13 : p1 ≠ p3) (h14 : p1 ≠ p4) (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    False := by
  obtain ⟨j, hc, he⟩ := M.pass i b
  exact M.nored ⟨i, b, _, j, hc,
    four_count n gs M.hcl i b p1 p2 p3 p4 h12 h13 h14 h23 h24 h34 h1 h2 h3 h4, he⟩

theorem Min.ndup (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2)
    (h13 : p1 ≠ p3) (h23 : p2 ≠ p3) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2)
    (h3 : RC n gs i b p3) (p j q k : ℕ) (hq : stF n gs i b p = Stat.wire q) (hnq : n ≤ q)
    (hk : stF n gs i b j = Stat.wire k) (hkq : k < q)
    (heq : ∀ y : Fin n → Bool, vl gs (ins i b y) p = vl gs (ins i b y) j) : False := by
  obtain ⟨jo, hc, he⟩ := M.pass i b
  have h3c : (passG n gs i b).length + 3 ≤ gs.length :=
    three_count n gs M.hcl i b p1 p2 p3 h12 h13 h23 h1 h2 h3
  have hqv : q < n + (passG n gs i b).length := by
    have h := ((inv_stF n gs M.hcl i b (fun _ => false)).2 p).1
    rw [show (elim n gs (statAt n i b, [])).1.getD p (Stat.const false) = Stat.wire q from hq]
      at h
    exact h
  have heq1 : ∀ y : Fin n → Bool,
      vl (passG n gs i b) y (n + (q - n)) = vl (passG n gs i b) y k := by
    intro y
    rw [show n + (q - n) = q by omega, ← st_val_wire n gs M.hcl i b p q hq y,
      ← st_val_wire n gs M.hcl i b j k hk y]
    exact heq y
  obtain ⟨y, y', hne⟩ := M.hnc i b
  obtain ⟨gs2, o2, hc2, hl2, he2⟩ := drop_alias n (passG n gs i b) hc jo (q - n) k (by omega)
    (by omega) heq1 ⟨y, y', by rw [he y, he y']; exact hne⟩
  exact M.nored ⟨i, b, gs2, o2, hc2, by omega, fun y => by rw [he2 y, he y]⟩

theorem Min.reader (M : Min n gs o) (i : Fin (n + 1)) (B : ℕ → Prop) (hi : B i) (ho : ¬ B o) :
    ∃ p g, gs[p]? = some g ∧ ¬ B (n + 1 + p) ∧ ∃ a ∈ g.inputs, B a := by
  apply exists_reader (n + 1) i B hi gs o ho
  by_contra hns
  refine M.hdep i (fun _ => false) ?_
  exact (agree_wiresFrom (Function.update (fun _ => false) i (!false)) (fun _ => false) gs _ _ _
    (agree_inputs _ _)).2.2 o (by
      intro k hk
      have : k ≠ i := fun e => hns (e ▸ hk)
      simp [Function.update_of_ne this])

theorem Min.cb (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (B : ℕ → Prop) (hi : B i)
    (hB : ∀ a, B a → IsC n gs i b a) :
    ∃ h1 h2, h1 ≠ h2 ∧ ¬ B (n + 1 + h1) ∧ ¬ B (n + 1 + h2) ∧ RC n gs i b h1 ∧ RC n gs i b h2 := by
  have ho : ¬ B o := fun h => by
    obtain ⟨c, hc⟩ := hB o h
    exact M.out i b c hc
  obtain ⟨h1, g1, hg1, hB1, a1, ha1, hBa1⟩ := M.reader i B hi ho
  have r1 : RC n gs i b h1 := ⟨g1, hg1, a1, ha1, hB a1 hBa1⟩
  by_cases hex : ∃ h2 g2, h2 ≠ h1 ∧ gs[h2]? = some g2 ∧ ¬ B (n + 1 + h2) ∧ ∃ a ∈ g2.inputs, B a
  · obtain ⟨h2, g2, hne, hg2, hB2, a2, ha2, hBa2⟩ := hex
    exact ⟨h1, h2, Ne.symm hne, hB1, hB2, r1, ⟨g2, hg2, a2, ha2, hB a2 hBa2⟩⟩
  by_cases hc1 : IsC n gs i b (n + 1 + h1)
  · obtain ⟨h2, g2, hg2, hB2, a2, ha2, hBa2⟩ := M.reader i (fun a => B a ∨ a = n + 1 + h1)
      (Or.inl hi) (fun h => h.elim ho (fun e => by
        obtain ⟨c, hc⟩ := hc1
        exact M.out i b c (by rw [e]; exact hc)))
    have hB2' : ¬ (B (n + 1 + h2) ∨ n + 1 + h2 = n + 1 + h1) := hB2
    have hBa2' : B a2 ∨ a2 = n + 1 + h1 := hBa2
    refine ⟨h1, h2, fun e => hB2' (Or.inr (by rw [e])), hB1, fun h => hB2' (Or.inl h), r1,
      g2, hg2, a2, ha2, ?_⟩
    rcases hBa2' with h | h
    · exact hB a2 h
    · rw [h]; exact hc1
  · exfalso
    obtain ⟨c1, hc1'⟩ := hB a1 hBa1
    obtain ⟨hop, _, w, hw, hwn⟩ := st_shape n gs M.hcl i b h1 g1 hg1 a1 ha1 c1 hc1'
      (fun c' h => hc1 ⟨c', h⟩)
    have hBw : ¬ B w := fun h => by
      obtain ⟨c, hc⟩ := hB w h
      exact hwn c hc
    have hwlt : w < n + 1 + h1 := (M.hcl h1 g1 hg1).lt w hw
    have hl1 : h1 < gs.length := (List.getElem?_eq_some_iff.1 hg1).1
    obtain ⟨u, hu⟩ := takes gs M.m1 w (by omega) (fixBit g1)
    apply M.hdep i u
    refine agree_B gs M.hcl _ _ B (o + 1) ?_ ?_ o (by omega) ho
    · intro j hj hBj
      rw [vl_input gs _ j hj, vl_input gs _ j hj]
      exact Function.update_of_ne
        (fun e => hBj (by rw [show j = (i : ℕ) from congrArg Fin.val e]; exact hi)) _ _
    · intro p g hp _ hBp hr hear
      obtain ⟨a, ha, hBa⟩ := hr
      have hp1 : p = h1 := by
        by_contra hne
        exact hex ⟨p, g, hne, hp, hBp, a, ha, hBa⟩
      rw [hp1] at hear ⊢
      rw [vl_abs gs M.hcl _ h1 g1 hg1 hop w hw (by rw [hear w hwlt hBw]; exact hu),
        vl_abs gs M.hcl u h1 g1 hg1 hop w hw hu]

theorem Min.one_const (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (p q : ℕ) (hpq : p ≠ q)
    (gp gq : Gate) (hp : gs[p]? = some gp) (hq : gs[q]? = some gq)
    (cp : IsC n gs i b (n + 1 + p)) (cq : IsC n gs i b (n + 1 + q)) : False := by
  obtain ⟨h1, h2, h12, hB1, hB2, r1, r2⟩ := M.cb i b
    (fun a => a = (i : ℕ) ∨ a = n + 1 + p ∨ a = n + 1 + q) (Or.inl rfl) (by
      intro a ha
      rcases ha with e | e | e
      · rw [e]; exact ⟨b, stF_self n gs i b⟩
      · rw [e]; exact cp
      · rw [e]; exact cq)
  have hB1' : ¬ (n + 1 + h1 = (i : ℕ) ∨ n + 1 + h1 = n + 1 + p ∨ n + 1 + h1 = n + 1 + q) := hB1
  have hB2' : ¬ (n + 1 + h2 = (i : ℕ) ∨ n + 1 + h2 = n + 1 + p ∨ n + 1 + h2 = n + 1 + q) := hB2
  exact M.nf4 i b p q h1 h2 hpq (fun e => hB1' (Or.inr (Or.inl (by rw [e]))))
    (fun e => hB2' (Or.inr (Or.inl (by rw [e])))) (fun e => hB1' (Or.inr (Or.inr (by rw [e]))))
    (fun e => hB2' (Or.inr (Or.inr (by rw [e])))) h12
    (rc_of_const n gs M.hcl i b p gp hp cp) (rc_of_const n gs M.hcl i b q gq hq cq) r1 r2

theorem Min.reader_const (M : Min n gs o) (i : Fin (n + 1)) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hr : (i : ℕ) ∈ g.inputs) : IsC n gs i (fixBit g) (n + 1 + p) :=
  const_read n gs M.hcl i _ p g hp i hr (stF_self n gs i _)

theorem Min.no_not (M : Min n gs o) (i : Fin (n + 1)) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hop : g.op = GateOp.not) (hr : (i : ℕ) ∈ g.inputs) : False := by
  have hin : g.inputs = [(i : ℕ)] := by
    rcases M.hcl p g hp with ⟨_, j, _, hin⟩ | ⟨h, _⟩
    · rw [hin] at hr
      have e : (i : ℕ) = j := by simpa using hr
      rw [hin, e]
    · rcases h with h | h <;> rw [hop] at h <;> cases h
  have hN : ∀ b, IsC n gs i b (n + 1 + p) := fun b =>
    st_allconst n gs M.hcl i b p g hp (fun a ha => by
      rw [hin] at ha
      have e : a = (i : ℕ) := by simpa using ha
      rw [e]; exact ⟨b, stF_self n gs i b⟩)
  have hNv : ∀ b, stF n gs i b (n + 1 + p) = Stat.const (!b) := by
    intro b
    obtain ⟨c, hc⟩ := hN b
    have h1 := st_val_const n gs M.hcl i b (n + 1 + p) c hc (fun _ => false)
    have h2 : vl gs (ins i b fun _ => false) (i : ℕ) = b := by
      rw [vl_input gs _ i i.isLt]; simp [ins]
    have h3 : c = !b := by
      rw [← h1, vl_gate gs M.hcl _ p g hp, hop, hin]
      simp [GateOp.eval, h2]
    rw [hc, h3]
  have ho : ¬ (o = (i : ℕ) ∨ o = n + 1 + p) := by
    intro h
    rcases h with e | e
    · exact M.out i false false (by rw [e]; exact stF_self n gs i false)
    · exact M.out i false _ (by rw [e]; exact hNv false)
  obtain ⟨q, gq, hq, hBq, a, ha, hBa⟩ :=
    M.reader i (fun a => a = (i : ℕ) ∨ a = n + 1 + p) (Or.inl rfl) ho
  have hBq' : ¬ (n + 1 + q = (i : ℕ) ∨ n + 1 + q = n + 1 + p) := hBq
  have hBa' : a = (i : ℕ) ∨ a = n + 1 + p := hBa
  have hpq : p ≠ q := fun e => hBq' (Or.inr (by rw [e]))
  have hcq : ∃ b, IsC n gs i b (n + 1 + q) := by
    rcases hBa' with e | e
    · exact ⟨fixBit gq, M.reader_const i q gq hq (e ▸ ha)⟩
    · refine ⟨!fixBit gq, const_read n gs M.hcl i _ q gq hq (n + 1 + p) (e ▸ ha) ?_⟩
      rw [hNv]; simp
  obtain ⟨b0, hb0⟩ := hcq
  exact M.one_const i b0 p q hpq g gq hp hq (hN b0) hb0

theorem Min.forced (M : Min n gs o) (X : Fin (n + 1)) (p q : ℕ) (gp : Gate)
    (hp : gs[p]? = some gp) (hXp : (X : ℕ) ∈ gp.inputs)
    (hR : ∀ p' g', gs[p']? = some g' → (X : ℕ) ∈ g'.inputs → p' = p ∨ p' = q)
    (hqo : o ≠ n + 1 + q) (u : Fin (n + 1) → Bool)
    (hq : vl gs (Function.update u X (!u X)) (n + 1 + q) = vl gs u (n + 1 + q) ∨
      ∀ (p' : ℕ) (g' : Gate), gs[p']? = some g' → (n + 1 + q) ∉ g'.inputs) :
    vl gs u (n + 1 + p) = u X := by
  by_contra hne
  have hX : vl gs u X = u X := vl_input gs u X X.isLt
  have hX' : vl gs (Function.update u X (!u X)) X = !u X := by
    rw [vl_input gs _ X X.isLt]; simp
  have key : vl gs (Function.update u X (!u X)) (n + 1 + p) = vl gs u (n + 1 + p) := by
    rcases M.hcl p gp hp with ⟨hopn, _⟩ | ⟨hop, j, k, _, _, hin⟩
    · exact (M.no_not X p gp hp hopn hXp).elim
    · have e1 : ∀ v : Fin (n + 1) → Bool,
          vl gs v (n + 1 + p) = gp.op.eval [vl gs v j, vl gs v k] := by
        intro v
        rw [vl_gate gs M.hcl v p gp hp, hin]
        rfl
      rw [e1 u] at hne
      rw [e1 u, e1 (Function.update u X (!u X))]
      have hjk : (X : ℕ) = j ∨ (X : ℕ) = k := by rw [hin] at hXp; simpa using hXp
      rcases hjk with e | e
      · rw [← e, hX] at hne
        rw [← e, hX', hX]
        revert hne
        generalize vl gs (Function.update u X (!u X)) k = w'
        generalize vl gs u k = w
        generalize u X = x
        rcases hop with hop | hop <;> rw [hop] <;> cases x <;> cases w <;> cases w' <;>
          simp [GateOp.eval]
      · rw [← e, hX] at hne
        rw [← e, hX', hX]
        revert hne
        generalize vl gs (Function.update u X (!u X)) j = w'
        generalize vl gs u j = w
        generalize u X = x
        rcases hop with hop | hop <;> rw [hop] <;> cases x <;> cases w <;> cases w' <;>
          simp [GateOp.eval]
  apply M.hdep X u
  refine agree_B gs M.hcl _ _ (fun a => a = (X : ℕ) ∨ a = n + 1 + q) (o + 1) ?_ ?_ o (by omega) ?_
  · intro j hj hBj
    have hBj' : ¬ (j = (X : ℕ) ∨ j = n + 1 + q) := hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne (fun e => hBj' (Or.inl (congrArg Fin.val e))) _ _
  · intro p' g' hp' _ hB' hr hear
    have hB'' : ¬ (n + 1 + p' = (X : ℕ) ∨ n + 1 + p' = n + 1 + q) := hB'
    obtain ⟨a, ha, hBa⟩ := hr
    have hBa' : a = (X : ℕ) ∨ a = n + 1 + q := hBa
    by_cases hx : (X : ℕ) ∈ g'.inputs
    · rcases hR p' g' hp' hx with e | e
      · rw [e]; exact key
      · exact absurd (Or.inr (by rw [e])) hB''
    · rcases hq with hq | hq
      · apply vl_congr gs M.hcl _ _ p' g' hp'
        intro a' ha'
        by_cases e1 : a' = n + 1 + q
        · rw [e1]; exact hq
        · exact hear a' ((M.hcl p' g' hp').lt a' ha')
            (fun hb => (hb : a' = (X : ℕ) ∨ a' = n + 1 + q).elim (fun e => hx (e ▸ ha')) e1)
      · rcases hBa' with e | e
        · exact absurd (e ▸ ha) hx
        · exact absurd (e ▸ ha) (hq p' g' hp')
  · exact fun (h : o = (X : ℕ) ∨ o = n + 1 + q) => h.elim
      (fun e => M.out X false false (by rw [e]; exact stF_self n gs X false)) hqo

theorem Min.block2 (M : Min n gs o) (Z : Fin (n + 1)) (B : ℕ → Prop) (hZ : B Z) (ho : ¬ B o)
    (u : Fin (n + 1) → Bool) (ha hb : ℕ) (ga gb : Gate) (hga : gs[ha]? = some ga)
    (hgb : gs[hb]? = some gb)
    (hout : ∀ p' g', gs[p']? = some g' → ¬ B (n + 1 + p') → (∃ a ∈ g'.inputs, B a) →
      p' = ha ∨ p' = hb)
    (hopa : ga.op = GateOp.and ∨ ga.op = GateOp.or) (w : ℕ) (hw : w ∈ ga.inputs) (hBw : ¬ B w)
    (hv : vl gs u w = fixBit ga)
    (hagree : ∀ a ∈ gb.inputs, B a → vl gs (Function.update u Z (!u Z)) a = vl gs u a) :
    False := by
  apply M.hdep Z u
  refine agree_B gs M.hcl _ _ B (o + 1) ?_ ?_ o (by omega) ho
  · intro j hj hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne
      (fun e => hBj (by rw [show j = (Z : ℕ) from congrArg Fin.val e]; exact hZ)) _ _
  · intro p' g' hp' _ hB' hr hear
    rcases hout p' g' hp' hB' hr with e | e
    · rw [e] at hear ⊢
      have hwlt : w < n + 1 + ha := (M.hcl ha ga hga).lt w hw
      rw [vl_abs gs M.hcl _ ha ga hga hopa w hw (by rw [hear w hwlt hBw]; exact hv),
        vl_abs gs M.hcl u ha ga hga hopa w hw hv]
    · rw [e] at hear ⊢
      apply vl_congr gs M.hcl _ _ hb gb hgb
      intro a haa
      by_cases hBa : B a
      · exact hagree a haa hBa
      · exact hear a ((M.hcl hb gb hgb).lt a haa) hBa

theorem Min.before (M : Min n gs o) (Z : Fin (n + 1)) (B : ℕ → Prop) (hZ : B Z)
    (u : Fin (n + 1) → Bool) (w : ℕ) (hBw : ¬ B w)
    (hne : vl gs (Function.update u Z (!u Z)) w ≠ vl gs u w) :
    ∃ p' g', gs[p']? = some g' ∧ n + 1 + p' ≤ w ∧ ¬ B (n + 1 + p') ∧ ∃ a ∈ g'.inputs, B a := by
  by_contra hno
  apply hne
  refine agree_B gs M.hcl _ _ B (w + 1) ?_ ?_ w (by omega) hBw
  · intro j hj hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne
      (fun e => hBj (by rw [show j = (Z : ℕ) from congrArg Fin.val e]; exact hZ)) _ _
  · intro p' g' hp' hlt hB' hr _
    exact (hno ⟨p', g', hp', by omega, hB', hr⟩).elim

theorem Min.second (M : Min n gs o) (X Y : Fin (n + 1)) (hXY : X ≠ Y) (pG : ℕ) (gG : Gate)
    (hG : gs[pG]? = some gG) (hop : gG.op = GateOp.and ∨ gG.op = GateOp.or)
    (hY : (Y : ℕ) ∈ gG.inputs) :
    ∃ r gr, r ≠ pG ∧ gs[r]? = some gr ∧ (X : ℕ) ∈ gr.inputs := by
  by_contra hno
  have hu : ∀ v : Fin (n + 1) → Bool, v Y = fixBit gG → vl gs v (n + 1 + pG) = fixBit gG :=
    fun v hv => vl_abs gs M.hcl v pG gG hG hop Y hY (by rw [vl_input gs v Y Y.isLt]; exact hv)
  apply M.hdep X (fun _ => fixBit gG)
  refine agree_B gs M.hcl _ _ (fun a => a = (X : ℕ)) (o + 1) ?_ ?_ o (by omega) ?_
  · intro j hj hBj
    have hBj' : ¬ (j = (X : ℕ)) := hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne (fun e => hBj' (congrArg Fin.val e)) _ _
  · intro p g hp _ _ hr _
    obtain ⟨a, ha, hBa⟩ := hr
    have hBa' : a = (X : ℕ) := hBa
    have hpG : p = pG := by
      by_contra hne
      exact hno ⟨p, g, hne, hp, hBa' ▸ ha⟩
    rw [hpG]
    rw [hu _ (by rw [Function.update_of_ne hXY.symm]), hu _ rfl]
  · exact fun (e : o = (X : ℕ)) => M.out X false false (by rw [e]; exact stF_self n gs X false)

theorem Min.side (M : Min n gs o) (X Y : Fin (n + 1)) (hXY : X ≠ Y) (pG : ℕ) (gG : Gate)
    (hG : gs[pG]? = some gG) (hop : gG.op = GateOp.and ∨ gG.op = GateOp.or)
    (hX : (X : ℕ) ∈ gG.inputs) (hY : (Y : ℕ) ∈ gG.inputs) :
    ∃ r gr, r ≠ pG ∧ gs[r]? = some gr ∧ (X : ℕ) ∈ gr.inputs ∧
      (∀ p' g', gs[p']? = some g' → (X : ℕ) ∈ g'.inputs → p' = r ∨ p' = pG) ∧
      IsC n gs X (!fixBit gG) (n + 1 + r) ∧ fixBit gr = !fixBit gG ∧
      (gr.op = GateOp.and ∨ gr.op = GateOp.or) ∧ (n + 1 + pG) ∉ gr.inputs := by
  have cG : IsC n gs X (fixBit gG) (n + 1 + pG) := M.reader_const X pG gG hG hX
  obtain ⟨r, gr, hrG, hr, hXr⟩ := M.second X Y hXY pG gG hG hop hY
  have ncr : ¬ IsC n gs X (fixBit gG) (n + 1 + r) :=
    fun h => M.one_const X _ pG r (Ne.symm hrG) gG gr hG hr cG h
  have cr := M.reader_const X r gr hr hXr
  have hfr : fixBit gr = !fixBit gG := by
    by_contra hne
    apply ncr
    have e : fixBit gr = fixBit gG := by
      revert hne
      cases fixBit gr <;> cases fixBit gG <;> simp
    rw [← e]; exact cr
  have cr' : IsC n gs X (!fixBit gG) (n + 1 + r) := by rw [← hfr]; exact cr
  refine ⟨r, gr, hrG, hr, hXr, ?_, cr', hfr, ?_, ?_⟩
  · intro p' g' hp' hx
    by_contra hne
    have h1 : p' ≠ r := fun e => hne (Or.inl e)
    have h2 : p' ≠ pG := fun e => hne (Or.inr e)
    have cp := M.reader_const X p' g' hp' hx
    by_cases e : fixBit g' = fixBit gG
    · rw [e] at cp
      exact M.one_const X _ pG p' (Ne.symm h2) gG g' hG hp' cG cp
    · have e' : fixBit g' = !fixBit gG := by
        revert e
        cases fixBit g' <;> cases fixBit gG <;> simp
      rw [e'] at cp
      exact M.one_const X _ r p' (Ne.symm h1) gr g' hr hp' cr' cp
  · rcases M.hcl r gr hr with ⟨hopn, _⟩ | ⟨h, _⟩
    · exact (M.no_not X r gr hr hopn hXr).elim
    · exact h
  · intro hGr
    obtain ⟨c0, hc0⟩ := cG
    obtain ⟨_, _, w, hw, hwn⟩ := st_shape n gs M.hcl X (fixBit gG) r gr hr (n + 1 + pG) hGr c0 hc0
      (fun c' h => ncr ⟨c', h⟩)
    rcases two_inputs (M.hcl r gr hr) (X : ℕ) (n + 1 + pG) w hXr hGr
      (by have := X.isLt; omega) hw with e | e
    · exact hwn _ (by rw [e]; exact stF_self n gs X _)
    · exact hwn c0 (by rw [e]; exact hc0)

theorem Min.pair_false (M : Min n gs o) (X Y : Fin (n + 1)) (hXY : X ≠ Y) (pG : ℕ) (gG : Gate)
    (hG : gs[pG]? = some gG) (hop : gG.op = GateOp.and ∨ gG.op = GateOp.or)
    (hX : (X : ℕ) ∈ gG.inputs) (hY : (Y : ℕ) ∈ gG.inputs) : False := by
  have hXYn : (X : ℕ) ≠ (Y : ℕ) := fun e => hXY (Fin.ext e)
  obtain ⟨r, gr, hrG, hr, hXr, hRX, crX, hfr, hopr, hGr⟩ := M.side X Y hXY pG gG hG hop hX hY
  obtain ⟨r', gr', hr'G, hr', hYr', hRY, _, _, _, hGr'⟩ :=
    M.side Y X hXY.symm pG gG hG hop hY hX
  have cGX : IsC n gs X (fixBit gG) (n + 1 + pG) := M.reader_const X pG gG hG hX
  have cGY : IsC n gs Y (fixBit gG) (n + 1 + pG) := M.reader_const Y pG gG hG hY
  have hoX : o ≠ (X : ℕ) := fun e => M.out X false false (by rw [e]; exact stF_self n gs X false)
  have hoY : o ≠ (Y : ℕ) := fun e => M.out Y false false (by rw [e]; exact stF_self n gs Y false)
  have hoG : o ≠ n + 1 + pG := fun e => by
    have ⟨c, hc⟩ := cGX
    exact M.out X _ c (by rw [e]; exact hc)
  have hor : o ≠ n + 1 + r := fun e => by
    have ⟨c, hc⟩ := crX
    exact M.out X _ c (by rw [e]; exact hc)
  have hGv : ∀ (Z : Fin (n + 1)) (v : Fin (n + 1) → Bool), (Z : ℕ) ∈ gG.inputs →
      v Z = fixBit gG → vl gs v (n + 1 + pG) = fixBit gG :=
    fun Z v hZ hv => vl_abs gs M.hcl v pG gG hG hop Z hZ (by rw [vl_input gs v Z Z.isLt]; exact hv)
  have hrX : ∀ v : Fin (n + 1) → Bool, v X = fixBit gr → vl gs v (n + 1 + r) = fixBit gr :=
    fun v hv => vl_abs gs M.hcl v r gr hr hopr X hXr (by rw [vl_input gs v X X.isLt]; exact hv)
  have hGin : ∀ w ∈ gG.inputs, w = (X : ℕ) ∨ w = (Y : ℕ) :=
    fun w hw => two_inputs (M.hcl pG gG hG) X Y w hX hY hXYn hw
  have fX : ∀ u : Fin (n + 1) → Bool, u Y = fixBit gG → vl gs u (n + 1 + r) = u X := fun u hu =>
    M.forced X r pG gr hr hXr hRX hoG u (Or.inl (by
      rw [hGv Y _ hY (by rw [Function.update_of_ne hXY.symm]; exact hu), hGv Y u hY hu]))
  have hex1 : ∃ (h1 : ℕ) (g1 : Gate), gs[h1]? = some g1 ∧ (n + 1 + pG) ∈ g1.inputs := by
    by_contra hno
    refine M.m2 r gr hr X (by have := X.isLt; omega) (fun u => ?_)
    rw [vl_input gs u X X.isLt]
    exact M.forced X r pG gr hr hXr hRX hoG u
      (Or.inr (fun p' g' hp' hin => hno ⟨p', g', hp', hin⟩))
  obtain ⟨h1, g1, hg1, hGh1⟩ := hex1
  have h1G : h1 ≠ pG := fun e => by
    have := (M.hcl h1 g1 hg1).lt _ hGh1
    omega
  have h1r : h1 ≠ r := fun e => hGr (gate_eq hg1 hr e ▸ hGh1)
  have h1r' : h1 ≠ r' := fun e => hGr' (gate_eq hg1 hr' e ▸ hGh1)
  by_cases hrr : r = r'
  swap
  · by_cases hrc : RC n gs Y (fixBit gG) r
    · exact M.nf4 Y (fixBit gG) pG r' h1 r (Ne.symm hr'G) (Ne.symm h1G) (Ne.symm hrG)
        (Ne.symm h1r') (Ne.symm hrr) h1r ⟨gG, hG, Y, hY, _, stF_self n gs Y _⟩
        ⟨gr', hr', Y, hYr', _, stF_self n gs Y _⟩ ⟨g1, hg1, _, hGh1, cGY⟩ hrc
    · obtain ⟨q, hnq, hq⟩ := st_fresh n gs M.hcl Y (fixBit gG) r gr hr
        (fun a ha c hc => hrc ⟨gr, hr, a, ha, c, hc⟩)
      obtain ⟨k, hk, hkX⟩ := st_other n gs Y (fixBit gG) X hXY
      refine M.ndup Y (fixBit gG) pG r' h1 (Ne.symm hr'G) (Ne.symm h1G) (Ne.symm h1r')
        ⟨gG, hG, Y, hY, _, stF_self n gs Y _⟩ ⟨gr', hr', Y, hYr', _, stF_self n gs Y _⟩
        ⟨g1, hg1, _, hGh1, cGY⟩ (n + 1 + r) X q k hq hnq hkX (by omega) (fun y => ?_)
      rw [vl_input gs _ X X.isLt]
      exact fX _ (by simp [ins])
  · have hRY' : ∀ p' g', gs[p']? = some g' → (Y : ℕ) ∈ g'.inputs → p' = r ∨ p' = pG := by
      intro p' g' hp' hy
      rw [hrr]; exact hRY p' g' hp' hy
    have hex2 : ∃ (h2 : ℕ) (g2 : Gate), gs[h2]? = some g2 ∧ (n + 1 + r) ∈ g2.inputs := by
      by_contra hno
      refine M.m2 pG gG hG X (by have := X.isLt; omega) (fun u => ?_)
      rw [vl_input gs u X X.isLt]
      exact M.forced X pG r gG hG hX (fun p' g' hp' hx => (hRX p' g' hp' hx).symm) hor u
        (Or.inr (fun p' g' hp' hin => hno ⟨p', g', hp', hin⟩))
    obtain ⟨h2, g2, hg2, hrh2⟩ := hex2
    have hrG' : (n + 1 + r) ∉ gG.inputs := fun h => by
      rcases hGin _ h with e | e
      · have := X.isLt; omega
      · have := Y.isLt; omega
    have h2r : h2 ≠ r := fun e => by
      have := (M.hcl h2 g2 hg2).lt _ hrh2
      omega
    have h2G : h2 ≠ pG := fun e => hrG' (gate_eq hg2 hG e ▸ hrh2)
    have h1u : ∀ p' g', gs[p']? = some g' → (n + 1 + pG) ∈ g'.inputs → p' = h1 := by
      intro p' g' hp' hin
      by_contra hne
      have e1 : p' ≠ pG := fun e => by
        have := (M.hcl p' g' hp').lt _ hin
        omega
      have e2 : p' ≠ r := fun e => hGr (gate_eq hp' hr e ▸ hin)
      exact M.nf4 X (fixBit gG) pG r h1 p' (Ne.symm hrG) (Ne.symm h1G) (Ne.symm e1)
        (Ne.symm h1r) (Ne.symm e2) (Ne.symm hne) ⟨gG, hG, X, hX, _, stF_self n gs X _⟩
        ⟨gr, hr, X, hXr, _, stF_self n gs X _⟩ ⟨g1, hg1, _, hGh1, cGX⟩ ⟨g', hp', _, hin, cGX⟩
    have h2u : ∀ p' g', gs[p']? = some g' → (n + 1 + r) ∈ g'.inputs → p' = h2 := by
      intro p' g' hp' hin
      by_contra hne
      have e1 : p' ≠ pG := fun e => hrG' (gate_eq hp' hG e ▸ hin)
      have e2 : p' ≠ r := fun e => by
        have := (M.hcl p' g' hp').lt _ hin
        omega
      exact M.nf4 X (!fixBit gG) pG r h2 p' (Ne.symm hrG) (Ne.symm h2G) (Ne.symm e1)
        (Ne.symm h2r) (Ne.symm e2) (Ne.symm hne) ⟨gG, hG, X, hX, _, stF_self n gs X _⟩
        ⟨gr, hr, X, hXr, _, stF_self n gs X _⟩ ⟨g2, hg2, _, hrh2, crX⟩ ⟨g', hp', _, hin, crX⟩
    have n1X : ¬ IsC n gs X (fixBit gG) (n + 1 + h1) :=
      fun h => M.one_const X _ pG h1 (Ne.symm h1G) gG g1 hG hg1 cGX h
    have n2X : ¬ IsC n gs X (!fixBit gG) (n + 1 + h2) :=
      fun h => M.one_const X _ r h2 (Ne.symm h2r) gr g2 hr hg2 crX h
    have ⟨cg, hcg⟩ := cGX
    have ⟨cr, hcr⟩ := crX
    obtain ⟨hop1, hf1, w1, hw1, hw1n⟩ := st_shape n gs M.hcl X (fixBit gG) h1 g1 hg1 _ hGh1 cg hcg
      (fun c' h => n1X ⟨c', h⟩)
    obtain ⟨hop2, hf2, w2, hw2, hw2n⟩ := st_shape n gs M.hcl X (!fixBit gG) h2 g2 hg2 _ hrh2 cr
      hcr (fun c' h => n2X ⟨c', h⟩)
    have hcgv : cg = fixBit gG := by
      have h := st_val_const n gs M.hcl X (fixBit gG) (n + 1 + pG) cg hcg (fun _ => false)
      rw [hGv X _ hX (by simp [ins])] at h
      exact h.symm
    have hcrv : cr = fixBit gr := by
      have h := st_val_const n gs M.hcl X (!fixBit gG) (n + 1 + r) cr hcr (fun _ => false)
      rw [hrX _ (by simp [ins, hfr])] at h
      exact h.symm
    have f1 : fixBit g1 = !fixBit gG := by
      rw [hcgv] at hf1
      revert hf1
      cases fixBit g1 <;> cases fixBit gG <;> simp
    have f2 : fixBit g2 = fixBit gG := by
      rw [hcrv, hfr] at hf2
      revert hf2
      cases fixBit g2 <;> cases fixBit gG <;> simp
    have h12 : h1 ≠ h2 := fun e => by
      have e' : g1 = g2 := gate_eq hg1 hg2 e
      rw [e', f2] at f1
      revert f1
      cases fixBit gG <;> simp
    have hr1 : (n + 1 + r) ∉ g1.inputs := fun h => h12 (h2u h1 g1 hg1 h)
    have hG2 : (n + 1 + pG) ∉ g2.inputs := fun h => h12 (h1u h2 g2 hg2 h).symm
    have hX1 : (X : ℕ) ∉ g1.inputs := fun h => (hRX h1 g1 hg1 h).elim h1r h1G
    have hY1 : (Y : ℕ) ∉ g1.inputs := fun h => (hRY' h1 g1 hg1 h).elim h1r h1G
    have hX2 : (X : ℕ) ∉ g2.inputs := fun h => (hRX h2 g2 hg2 h).elim h2r h2G
    have hY2 : (Y : ℕ) ∉ g2.inputs := fun h => (hRY' h2 g2 hg2 h).elim h2r h2G
    have hBw1X : ¬ (w1 = (X : ℕ) ∨ w1 = n + 1 + pG ∨ w1 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hX1 (e ▸ hw1)
      · exact hw1n cg (by rw [e]; exact hcg)
      · exact hr1 (e ▸ hw1)
    have hBw1Y : ¬ (w1 = (Y : ℕ) ∨ w1 = n + 1 + pG ∨ w1 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hY1 (e ▸ hw1)
      · exact hw1n cg (by rw [e]; exact hcg)
      · exact hr1 (e ▸ hw1)
    have hBw2X : ¬ (w2 = (X : ℕ) ∨ w2 = n + 1 + pG ∨ w2 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hX2 (e ▸ hw2)
      · exact hG2 (e ▸ hw2)
      · exact hw2n cr (by rw [e]; exact hcr)
    have hBw2Y : ¬ (w2 = (Y : ℕ) ∨ w2 = n + 1 + pG ∨ w2 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hY2 (e ▸ hw2)
      · exact hG2 (e ▸ hw2)
      · exact hw2n cr (by rw [e]; exact hcr)
    have hout : ∀ (Z : Fin (n + 1)),
        (∀ p' g', gs[p']? = some g' → (Z : ℕ) ∈ g'.inputs → p' = r ∨ p' = pG) →
        ∀ p' g', gs[p']? = some g' →
          ¬ (n + 1 + p' = (Z : ℕ) ∨ n + 1 + p' = n + 1 + pG ∨ n + 1 + p' = n + 1 + r) →
          (∃ a ∈ g'.inputs, a = (Z : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) →
          p' = h1 ∨ p' = h2 := by
      intro Z hRZ p' g' hp' hB hr
      obtain ⟨a, ha, hBa⟩ := hr
      rcases hBa with e | e | e
      · exfalso
        rcases hRZ p' g' hp' (e ▸ ha) with e' | e'
        · exact hB (Or.inr (Or.inr (by rw [e'])))
        · exact hB (Or.inr (Or.inl (by rw [e'])))
      · exact Or.inl (h1u p' g' hp' (e ▸ ha))
      · exact Or.inr (h2u p' g' hp' (e ▸ ha))
    have hoBY : ¬ (o = (Y : ℕ) ∨ o = n + 1 + pG ∨ o = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hoY e
      · exact hoG e
      · exact hor e
    have A2 : ∀ u : Fin (n + 1) → Bool, vl gs u w2 = fixBit gG → u X = fixBit gG → False := by
      intro u hv hx
      refine M.block2 Y (fun a => a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl)
        hoBY u h2 h1 g2 g1 hg2 hg1 (fun p' g' hp' hB hr => (hout Y hRY' p' g' hp' hB hr).symm)
        hop2 w2 hw2 hBw2Y (by rw [f2]; exact hv) ?_
      intro a ha hBa
      rcases (hBa : a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) with e | e | e
      · exact absurd (e ▸ ha) hY1
      · rw [e, hGv X _ hX (by rw [Function.update_of_ne hXY]; exact hx), hGv X u hX hx]
      · exact absurd (e ▸ ha) hr1
    have A4 : ∀ u : Fin (n + 1) → Bool, vl gs u w1 = !fixBit gG → u X = !fixBit gG → False := by
      intro u hv hx
      refine M.block2 Y (fun a => a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl)
        hoBY u h1 h2 g1 g2 hg1 hg2 (hout Y hRY') hop1 w1 hw1 hBw1Y (by rw [f1]; exact hv) ?_
      intro a ha hBa
      rcases (hBa : a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) with e | e | e
      · exact absurd (e ▸ ha) hY2
      · exact absurd (e ▸ ha) hG2
      · rw [e, hrX _ (by rw [Function.update_of_ne hXY, hfr]; exact hx),
          hrX u (by rw [hfr]; exact hx)]
    have hl1 : h1 < gs.length := (List.getElem?_eq_some_iff.1 hg1).1
    have hl2 : h2 < gs.length := (List.getElem?_eq_some_iff.1 hg2).1
    have hw1lt := (M.hcl h1 g1 hg1).lt w1 hw1
    have hw2lt := (M.hcl h2 g2 hg2).lt w2 hw2
    have lt12 : h1 < h2 := by
      obtain ⟨u, hu⟩ := takes gs M.m1 w2 (by omega) (fixBit gG)
      have hx : u X = !fixBit gG := by
        have h := A2 u hu
        revert h
        cases u X <;> cases fixBit gG <;> simp
      have hne : vl gs (Function.update u X (!u X)) w2 ≠ vl gs u w2 := fun e =>
        A2 _ (by rw [e]; exact hu) (by simp [hx])
      obtain ⟨p', g', hp', hle, hB', hr'⟩ := M.before X
        (fun a => a = (X : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl) u w2 hBw2X hne
      rcases hout X hRX p' g' hp' hB' hr' with e | e
      · rw [e] at hle; omega
      · rw [e] at hle; omega
    have lt21 : h2 < h1 := by
      obtain ⟨u, hu⟩ := takes gs M.m1 w1 (by omega) (!fixBit gG)
      have hx : u X = fixBit gG := by
        have h := A4 u hu
        revert h
        cases u X <;> cases fixBit gG <;> simp
      have hne : vl gs (Function.update u X (!u X)) w1 ≠ vl gs u w1 := fun e =>
        A4 _ (by rw [e]; exact hu) (by simp [hx])
      obtain ⟨p', g', hp', hle, hB', hr'⟩ := M.before X
        (fun a => a = (X : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl) u w1 hBw1X hne
      rcases hout X hRX p' g' hp' hB' hr' with e | e
      · rw [e] at hle; omega
      · rw [e] at hle; omega
    omega

theorem Min.contra (M : Min n gs o) : False := by
  have hg0 : ∃ g0, gs[0]? = some g0 := by
    cases hgs : gs with
    | nil =>
      exfalso
      obtain ⟨p, g, hp, _⟩ := M.reader 0 (fun a => a = ((0 : Fin (n + 1)) : ℕ)) rfl
        (fun (e : o = ((0 : Fin (n + 1)) : ℕ)) =>
          M.out 0 false false (by rw [e]; exact stF_self n gs 0 false))
      rw [hgs] at hp
      simp at hp
    | cons g _ => exact ⟨g, rfl⟩
  obtain ⟨g0, h0⟩ := hg0
  rcases M.hcl 0 g0 h0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · exact M.no_not ⟨j, by omega⟩ 0 g0 h0 hop (by rw [hin]; simp)
  · by_cases hjk : j = k
    · refine M.m2 0 g0 h0 j (by omega) (fun u => ?_)
      rw [vl_gate gs M.hcl u 0 g0 h0, hin, hjk]
      rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
    · exact M.pair_false ⟨j, by omega⟩ ⟨k, by omega⟩ (fun e => hjk (congrArg Fin.val e)) 0 g0 h0
        hop (by rw [hin]; simp) (by rw [hin]; simp)

end

theorem par_lower4 : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasClean (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s → 4 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    classical
    have hex : ∃ t, HasClean (n + 1 + 1)
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) t := ⟨s, h⟩
    obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
    have hfs : Nat.find hex ≤ s := Nat.find_min' hex h
    have hev' : ∀ x : Fin (n + 1 + 1) → Bool, vl gs x o = xor (par (n + 1 + 1) x) c := hev
    have hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL (n + 1 + 1) gs' →
        (∀ x : Fin (n + 1 + 1) → Bool, vl gs' x o' = xor (par (n + 1 + 1) x) c) →
        gs.length ≤ gs'.length := by
      intro gs' o' hc' he'
      by_contra hlt
      exact Nat.find_min hex (m := gs'.length) (by omega) ⟨gs', o', hc', le_refl _, he'⟩
    suffices 4 * (n + 1) ≤ gs.length by omega
    by_contra hsmall
    have hncf : ∃ y y' : Fin (n + 1 + 1) → Bool, vl gs y o ≠ vl gs y' o := by
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      rw [hev', hev', par_snoc, par_snoc]
      cases par (n + 1) (fun _ => false) <;> cases c <;> simp
    have M : Min (n + 1) gs o :=
      { hcl := hcl
        hdep := by
          intro i u
          rw [hev', hev', par_flip]
          cases par (n + 1 + 1) u <;> cases c <;> simp
        hnc := by
          intro i b
          refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
          rw [hev', hev', par_insertNth, par_insertNth, par_snoc, par_snoc]
          cases par n (fun _ => false) <;> cases b <;> cases c <;> simp
        m1 := by
          intro p g hp c' hall
          have hpl : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
          obtain ⟨gs', o', hc', hl', he'⟩ := drop_const (n + 1 + 1) gs hcl o p c' hpl hall hncf
          have := hmin gs' o' hc' (fun x => by rw [he' x]; exact hev' x)
          omega
        m2 := by
          intro p g hp j hj hall
          have hpl : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
          obtain ⟨gs', o', hc', hl', he'⟩ :=
            drop_alias (n + 1 + 1) gs hcl o p j hpl hj hall hncf
          have := hmin gs' o' hc' (fun x => by rw [he' x]; exact hev' x)
          omega
        nored := by
          rintro ⟨i, b, gs', o', hc', hl', he'⟩
          have h' : HasClean (n + 1)
              (fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) (xor b c)) gs'.length :=
            ⟨gs', o', hc', le_refl _, fun y => by
              show vl gs' y o' = _
              rw [he' y, hev', par_insertNth, Bool.xor_assoc]⟩
          have := ih _ _ h'
          omega }
    exact M.contra

theorem parity_lower4 : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    4 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have hnc : ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y
          ≠ (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y' := by
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    have := par_lower4 n false s (clean_of (n + 1) _ s hnc h')
    omega

end PEqualNP.Outside.L_clb_127.X25689.OldParity
namespace PEqualNP.Outside.L_clb_127.X25689.Lit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical

def applySign (s v : Bool) := if s then !v else v

noncomputable def trace (N : Nat) (C : Circuit) (w : Nat) : Nat × Bool :=
  if N≤w ∧ w-N<C.size then
    let g:=gateAt C (w-N)
    let v:=g.inputs.headD w
    if g.op=.not then
      if h : v<w then
        let a:=trace N C v
        (a.1,!a.2)
      else (w,false)
    else (w,false)
  else (w,false)
termination_by w
decreasing_by exact h

theorem low {N : Nat} (C : Circuit) {w : Nat} (h : w<N) : trace N C w=(w,false) := by
  rw [trace];simp [show ¬N≤w by omega]

theorem binary {N : Nat} {C : Circuit} {j : Nat} (h : j<C.size) (op : (gateAt C j).op≠.not) :
    trace N C (N+j)=(N+j,false) := by
  rw [trace];simp [h,op]

theorem unary {N : Nat} {C : Circuit} {j v : Nat} (h : j<C.size) (op : (gateAt C j).op=.not)
    (pin : (gateAt C j).inputs=[v]) (lt : v<N+j) :
    trace N C (N+j)=((trace N C v).1,!(trace N C v).2) := by
  rw [trace];simp [h,op,pin,lt]

theorem below (N : Nat) (C : Circuit) (w : Nat) : (trace N C w).1≤w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rw [trace]
    split <;> dsimp
    · split
      · split
        · rename_i small
          exact (ih _ small).trans (Nat.le_of_lt small)
        · rfl
      · rfl
    · rfl

theorem opAt {N : Nat} {C : Circuit} (good : ∀g∈C.gates,Good False g) (j : Nat) (h : j<C.size) :
    ((gateAt C j).op=.not ∧ ∃v,(gateAt C j).inputs=[v]) ∨
    (((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧ ∃a b,a≠b ∧ (gateAt C j).inputs=[a,b]) := by
  have mem : gateAt C j∈C.gates:=by rw [show gateAt C j=C.gates[j] from List.getD_eq_getElem _ _ h];exact List.getElem_mem h
  exact (good _ mem).1

theorem value {N : Nat} {C : Circuit} (good : ∀g∈C.gates,Good False g) (back : ReadsBack N C)
    (x : List Bool) (len : x.length=N) (w : Nat) (ok : w<N+C.size) :
    let V:=fun i=>(run C.gates x).getD i false
    V w=applySign (trace N C w).2 (V (trace N C w).1) := by
  dsimp only
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w<N
    · rw [low C raw];rfl
    let j:=w-N
    have eq : N+j=w:=Nat.add_sub_of_le (by omega)
    have idx : j<C.size:=by dsimp [j];omega
    rcases opAt (N:=N) good j idx with ⟨op,v,pin⟩|⟨op,_⟩
    · have lt:=back j idx v (by simp [pin])
      rw [←eq,unary idx op pin lt,gv N C back x len j idx]
      have hv:=ih v (by omega) (by omega)
      cases s : (trace N C v).2 <;> simp [op,pin,GateOp.eval,applySign,s] at hv ⊢ <;> simp [hv]
    · have ne : (gateAt C j).op≠.not:=by rcases op with e|e <;> simp [e]
      rw [←eq,binary idx ne];rfl

theorem roots {N : Nat} {C : Circuit} (good : ∀g∈C.gates,Good False g) (back : ReadsBack N C)
    (w : Nat) (ok : w<N+C.size) : (trace N C w).1<N ∨
    ∃ j<C.size,(gateAt C j).op≠.not ∧ (trace N C w).1=N+j := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w<N
    · exact Or.inl ((below N C w).trans_lt raw)
    let j:=w-N
    have eq : N+j=w:=Nat.add_sub_of_le (by omega)
    have idx : j<C.size:=by dsimp [j];omega
    rcases opAt (N:=N) good j idx with ⟨op,v,pin⟩|⟨op,_⟩
    · have lt:=back j idx v (by simp [pin])
      rw [←eq,unary idx op pin lt]
      exact ih v (by omega) (by omega)
    · have ne : (gateAt C j).op≠.not:=by rcases op with e|e <;> simp [e]
      exact Or.inr ⟨j,idx,ne,by rw [←eq,binary idx ne]⟩
end PEqualNP.Outside.L_clb_127.X25689.Lit

namespace PEqualNP.Outside.L_clb_127.X25689.Lit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical

abbrev V {N : Nat} (C : Circuit) (x : Fin N→Bool) (w : Nat) := (run C.gates (List.ofFn x)).getD w false
def ReadsStem (N : Nat) (C : Circuit) (j i : Nat) := ∃w∈(gateAt C j).inputs,(trace N C w).1=i

theorem rawV {N} (C : Circuit) (x : Fin N→Bool) (i : Fin N) : V C x i.val=x i := by
  rw [V,run_input _ _ _ (by simpa using i.isLt)];exact readFn x i

theorem literalV {N} {C : Circuit} (good : ∀g∈C.gates,Good False g) (back : ReadsBack N C)
    (x : Fin N→Bool) (w : Nat) (ok : w<N+C.size) (i : Fin N) (atRaw : (trace N C w).1=i.val) :
    V C x w=applySign (trace N C w).2 (x i) := by
  have v:=value good back (List.ofFn x) List.length_ofFn w ok
  change V C x w=applySign _ (V C x _) at v
  rwa [atRaw,rawV] at v

theorem agree {N : Nat} {C : Circuit} (good : ∀g∈C.gates,Good False g) (back : ReadsBack N C)
    (i : Fin N) (x y : Fin N→Bool) (same : ∀a,a≠i → x a=y a)
    (held : ∀j<C.size,(gateAt C j).op≠.not → ReadsStem N C j i.val → V C x (N+j)=V C y (N+j))
    (w : Nat) (ok : w<N+C.size) (off : (trace N C w).1≠i.val) : V C x w=V C y w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w<N
    · rw [low C raw] at off
      let a : Fin N:=⟨w,raw⟩
      exact (rawV C x a).trans ((same a (fun e=>off (congrArg Fin.val e))).trans (rawV C y a).symm)
    let j:=w-N
    have eq : N+j=w:=Nat.add_sub_of_le (by omega)
    have idx : j<C.size:=by dsimp [j];omega
    rcases opAt (N:=N) good j idx with ⟨op,v,pin⟩|⟨op,_⟩
    · have lt:=back j idx v (by simp [pin])
      rw [←eq,unary idx op pin lt] at off
      have s:=ih v (by omega) (by omega) off
      rw [←eq];unfold V at s ⊢
      rw [gv N C back _ List.length_ofFn j idx,gv N C back _ List.length_ofFn j idx]
      simp [op,pin,GateOp.eval] <;> simpa [List.getD_eq_getElem?_getD] using s
    · have ne : (gateAt C j).op≠.not:=by rcases op with e|e <;> simp [e]
      by_cases present : ReadsStem N C j i.val
      · exact eq ▸ held j idx ne present
      rw [←eq];unfold V
      rw [gv N C back _ List.length_ofFn j idx,gv N C back _ List.length_ofFn j idx]
      congr 1
      apply List.map_congr_left
      intro v pin
      have lt:=back j idx v pin
      exact ih v (by omega) (by omega) (fun e=>present ⟨v,pin,e⟩)

theorem nextBinary {N : Nat} {C : Circuit} (good : ∀g∈C.gates,Good False g) (back : ReadsBack N C)
    (live : ∀i : Fin C.gates.length, N+i.val≠C.output → ∃ j : Fin C.gates.length,i<j ∧ reads (C.gates.get j) (N+i.val))
    (base : Nat) (notOut : (trace N C C.output).1≠base) (j : Nat) (idx : j<C.size)
    (root : (trace N C (N+j)).1=base) :
    ∃r<C.size,j<r ∧ (gateAt C r).op≠.not ∧ ReadsStem N C r base := by
  have ne : N+j≠C.output:=by intro eq;exact notOut (eq ▸ root)
  obtain ⟨r,after,later⟩:=live ⟨j,idx⟩ ne
  have opEq : C.gates.get r=gateAt C r.val:=(List.getD_eq_getElem _ _ r.isLt).symm
  rw [opEq] at later
  have member : gateAt C r.val∈C.gates:=by rw [←opEq];exact List.getElem_mem r.isLt
  have pin:=(good_read (good _ member) _).mp later
  have lt : j<r.val:=after
  rcases opAt (N:=N) good r.val r.isLt with ⟨op,v,hv⟩|⟨op,_⟩
  · have eq : N+j=v:=by simpa [hv] using pin
    have below:=back r.val r.isLt v (by simp [hv])
    have newRoot : (trace N C (N+r.val)).1=base:=by rw [unary r.isLt op hv below,←eq];exact root
    obtain ⟨k,hk,more,opr,read⟩:=nextBinary good back live base notOut r.val r.isLt newRoot
    exact ⟨k,hk,by omega,opr,read⟩
  · exact ⟨r.val,r.isLt,lt,by rcases op with h|h <;> simp [h],N+j,pin,root⟩
termination_by C.size-j
decreasing_by have h : r.val<C.size:=r.isLt;omega
end PEqualNP.Outside.L_clb_127.X25689.Lit

namespace PEqualNP.Outside.L_clb_127.X25689.Lit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical

theorem costElided (C : Circuit) (F : Finset Nat) (sites : ∀j∈F,j<C.size ∧ (gateAt C j).op≠.not) :
    remaining bin C F C.size+F.card=listed bin C.gates := by
  classical
  have filt : (Finset.range C.size).filter (·∈F)=F := by
    ext j;simp only [Finset.mem_filter,Finset.mem_range];exact ⟨fun h=>h.2,fun h=>⟨(sites j h).1,h⟩⟩
  have card : F.card=∑j∈Finset.range C.size,if j∈F then 1 else 0:=by rw [←Finset.card_filter,filt]
  rw [card,←full_price bin C];unfold remaining
  rw [←Finset.sum_add_distrib];apply Finset.sum_congr rfl
  intro j _
  by_cases mem : j∈F
  · simp [mem,bin,(sites j mem).2]
  · simp [mem]

theorem folded {X : Type} (n m : Nat) (C : Circuit) (fan : FanInTwo C)
    (src : X→List Bool) (dst : X→List Bool) (hs : ∀x,(src x).length=n) (ht : ∀x,(dst x).length=m)
    (raw : ∀ w<n,(∃b,∀x,(src x).getD w false=b) ∨ ∃t,t < m ∧ ∀x,(src x).getD w false=(dst x).getD t false)
    (nc : ¬∃b,∀x,C.eval (src x)=b) (F : Finset Nat) (sites : ∀j∈F,j<C.size ∧ (gateAt C j).op≠.not)
    (fold : ∀j∈F,collapses (fun x w=>(run C.gates (src x)).getD w false) (n+j)
      (fun x=>(run C.gates (src x)).getD (n+j) false)) :
    ∃D : Circuit,FanInTwo D ∧ listed bin D.gates+F.card≤listed bin C.gates ∧ ∀x,D.eval (dst x)=C.eval (src x) := by
  obtain ⟨D,good,_,_,prices,values⟩:=engineWeighted False n m C src dst hs ht F fan False.elim raw nc
    (fun j h=>⟨(sites j h).1,fold j h⟩)
  have spent:=prices bin
  have total:=costElided C F sites
  exact ⟨D,good_fan good,by omega,values⟩

theorem restrictRaw {n : Nat} (i : Fin (n+1)) (v : Bool) (w : Nat) (h : w<n+1) :
    (∃b,∀y : Fin n→Bool,(List.ofFn (Fin.insertNth i v y)).getD w false=b) ∨
    ∃t,t<n ∧ ∀y : Fin n→Bool,(List.ofFn (Fin.insertNth i v y)).getD w false=(List.ofFn y).getD t false := by
  let j : Fin (n+1):=⟨w,h⟩
  rcases Fin.eq_self_or_eq_succAbove i j with eq|⟨k,eq⟩
  · refine Or.inl ⟨v,fun y=>?_⟩
    change (List.ofFn _).getD j.val false=v
    rw [readFn,eq,Fin.insertNth_apply_same]
  · refine Or.inr ⟨k.val,k.isLt,fun y=>?_⟩
    change (List.ofFn _).getD j.val false=(List.ofFn _).getD k.val false
    rw [readFn,readFn,eq,Fin.insertNth_apply_succAbove]

theorem outputBound {N} (C : Circuit) (nc : ¬∃v,∀x : Fin N→Bool,C.eval (List.ofFn x)=v) : C.output<N+C.size := by
  by_contra! far
  exact nc ⟨false,fun x=>past C.gates (List.ofFn x) C.output (by rw [List.length_ofFn];exact far)⟩

theorem outputNotRaw {N} {C : Circuit} (good : ∀g∈C.gates,Good False g) (back : ReadsBack N C)
    (two : 2≤N) (ok : C.output<N+C.size)
    (sensitive : ∀i : Fin N,∀x : Fin N→Bool, V C (Function.update x i (!x i)) C.output≠V C x C.output) :
    ∀ i : Fin N,(trace N C C.output).1≠i.val := by
  intro i root
  let j : Fin N:=if i.val=0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
  have ne : i≠j:=by
    intro eq;have h:=congrArg Fin.val eq;by_cases z : i.val=0 <;> simp [j,z] at h <;> omega
  let x : Fin N→Bool:=fun _=>false
  have y:=literalV good back (Function.update x j (!x j)) C.output ok i root
  have z:=literalV good back x C.output ok i root
  exact sensitive j x (by rw [y,z,Function.update_of_ne ne])
end PEqualNP.Outside.L_clb_127.X25689.Lit

namespace PEqualNP.Outside.L_clb_127.X25689.Lit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical

noncomputable def absorb (g : Gate) : Bool := decide (g.op=GateOp.or)

theorem apply_twice (s v : Bool) : applySign s (applySign s v)=v := by cases s <;> cases v <;> rfl

theorem controlled (g : Gate) (op : g.op=.and ∨ g.op=.or) (a b w : Nat) (pins : g.inputs=[a,b])
    (read : w∈g.inputs) (z : Nat→Bool) (value : z w=absorb g) : g.op.eval (g.inputs.map z)=absorb g := by
  have mem : w=a ∨ w=b:=by simpa [pins] using read
  rcases mem with h|h <;> subst w <;> rcases op with e|e <;> simp [absorb,e,pins,GateOp.eval] at value ⊢ <;> simp [value]

theorem binaryPins {N : Nat} {C : Circuit} (good : ∀g∈C.gates,Good False g) (j : Nat) (idx : j<C.size)
    (ne : (gateAt C j).op≠.not) : ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    ∃a b,a≠b ∧ (gateAt C j).inputs=[a,b] := by
  rcases opAt (N:=N) good j idx with ⟨h,_⟩|h
  · contradiction
  · exact h

theorem another {N : Nat} {C : Circuit} (good : ∀g∈C.gates,Good False g) (back : ReadsBack N C)
    (i k : Fin N) (ik : i≠k) (j v : Nat) (idx : j<C.size) (ne : (gateAt C j).op≠.not)
    (pin : v∈(gateAt C j).inputs) (other : (trace N C v).1=k.val)
    (ok : C.output<N+C.size) (off : (trace N C C.output).1≠i.val)
    (sensitive : ∀x : Fin N→Bool,V C (Function.update x i (!x i)) C.output≠V C x C.output) :
    ∃r<C.size,r≠j ∧ (gateAt C r).op≠.not ∧ ReadsStem N C r i.val := by
  classical
  by_contra! none
  let g:=gateAt C j
  let x : Fin N→Bool:=fun _=>applySign (trace N C v).2 (absorb g)
  let y:=Function.update x i (!x i)
  have limit : v<N+C.size:=by have l:=back j idx v pin;omega
  have xval : V C x v=absorb g:=(literalV good back x v limit k other).trans (apply_twice _ _)
  have yval : V C y v=absorb g := by
    rw [literalV good back y v limit k other]
    unfold y;rw [Function.update_of_ne (Ne.symm ik)];exact apply_twice _ _
  obtain ⟨op,a,b,_,inputs⟩:=binaryPins (N:=N) good j idx ne
  have killed (z : Fin N→Bool) (h : V C z v=absorb g) : V C z (N+j)=absorb g :=
    (gv N C back _ List.length_ofFn j idx).trans (controlled g op a b v inputs pin _ h)
  have held (r) (h : r<C.size) (no : (gateAt C r).op≠.not) (reads : ReadsStem N C r i.val) :
      V C y (N+r)=V C x (N+r) := by
    by_cases eq : r=j
    · subst r;exact (killed y yval).trans (killed x xval).symm
    · exact False.elim (none r h eq no reads)
  apply sensitive x
  exact agree good back i y x (fun a h=>Function.update_of_ne h _ _) held C.output ok off

theorem triple {n : Nat} {C : Circuit} (good : ∀g∈C.gates,Good False g) (back : ReadsBack (n+1) C)
    (live : ∀i : Fin C.gates.length,n+1+i.val≠C.output → ∃j : Fin C.gates.length,i<j ∧ reads (C.gates.get j) (n+1+i.val))
    (i : Fin (n+1)) (j r : Nat) (less : j<r) (idx : r<C.size)
    (jbin : (gateAt C j).op≠.not) (rbin : (gateAt C r).op≠.not)
    (first : ReadsStem (n+1) C j i.val) (second : ReadsStem (n+1) C r i.val)
    (outOK : C.output<n+1+C.size) (nc : ∀b,¬∃v,∀y : Fin n→Bool,V C (Fin.insertNth i b y) C.output=v) :
    ∃b,∃D : Circuit,FanInTwo D ∧ listed bin D.gates+3≤listed bin C.gates ∧
      ∀y : Fin n→Bool,D.eval (List.ofFn y)=C.eval (List.ofFn (Fin.insertNth i b y)) := by
  obtain ⟨v,vr,root⟩:=second
  let N:=n+1
  let val:=applySign (trace N C v).2 (absorb (gateAt C r))
  let src:=fun y : Fin n→Bool=>List.ofFn (Fin.insertNth i val y)
  let W:=fun (y : Fin n→Bool) w=>(run C.gates (src y)).getD w false
  have atI (w) (h : w<N+C.size) (eq : (trace N C w).1=i.val) (y : Fin n→Bool) :
      W y w=applySign (trace N C w).2 val := by
    have z:=literalV good back (Fin.insertNth i val y) w h i eq
    simpa only [Fin.insertNth_apply_same] using z
  obtain ⟨op,a,b,_,pins⟩:=binaryPins (N:=N) good r idx rbin
  have stable (y : Fin n→Bool) : W y (N+r)=absorb (gateAt C r) := by
    have h:=back r idx v vr
    exact (gv N C back _ List.length_ofFn r idx).trans (controlled _ op a b v pins vr (W y)
      ((atI v (by omega) root y).trans (apply_twice _ _)))
  have endRoot : (trace N C C.output).1≠N+r := by
    intro out
    apply nc val
    refine ⟨applySign (trace N C C.output).2 (absorb (gateAt C r)),fun y=>?_⟩
    have v:=value good back (src y) List.length_ofFn C.output outOK
    change W y C.output=applySign _ (W y _) at v
    rwa [out,stable y] at v
  obtain ⟨q,qidx,rq,qbin,w,wq,wroot⟩:=nextBinary good back live (N+r) endRoot r idx (by rw [binary idx rbin])
  let F : Finset Nat:={j,r,q}
  have ji : j<C.size:=by omega
  have sites (p) (hp : p∈F) : p<C.size ∧ (gateAt C p).op≠.not := by
    simp only [F,Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with h|h|h <;> subst p <;> first | exact ⟨ji,jbin⟩ | exact ⟨idx,rbin⟩ | exact ⟨qidx,qbin⟩
  have touched (p) (hp : p∈F) : ∃t∈(gateAt C p).inputs,FixedAt W t := by
    simp only [F,Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with eq|eq|eq
    · subst p
      obtain ⟨t,pin,rt⟩:=first
      exact ⟨t,pin,_,atI t (by have h:=back j ji t pin;omega) rt⟩
    · subst p
      exact ⟨v,vr,_,atI v (by have h:=back r idx v vr;omega) root⟩
    · subst p
      refine ⟨w,wq,applySign (trace N C w).2 (absorb (gateAt C r)),fun y=>?_⟩
      have limit:=back q qidx w wq
      have z:=value good back (src y) List.length_ofFn w (by omega)
      change W y w=applySign _ (W y _) at z
      rwa [wroot,stable y] at z
  have fold (p) (hp : p∈F) : collapses W (N+p) (fun y=>W y (N+p)) := by
    obtain ⟨h,nb⟩:=sites _ hp
    obtain ⟨t,pin,b,fixed⟩:=touched _ hp
    obtain ⟨op,a,b',_,inputs⟩:=binaryPins (N:=N) good p h nb
    have e : ∀y,W y (N+p)=(gateAt C p).op.eval ((gateAt C p).inputs.map (W y)):=fun y=>gv N C back _ List.length_ofFn p h
    have z:=when_read W (gateAt C p) (N+p) t b (by tauto) (by simp [inputs]) (back p h)
      (Or.inr ⟨nb,pin⟩) fixed
    simpa only [e] using z
  obtain ⟨D,fan,cost,sem⟩:=folded N n C (good_fan good) src List.ofFn (fun _=>List.length_ofFn)
    (fun _=>List.length_ofFn) (restrictRaw i val) (nc val) F sites fold
  have sc : F.card=3:=by simp [F,show j≠r by omega,show r≠q by omega,show j≠q by omega]
  exact ⟨val,D,fan,by rwa [sc] at cost,sem⟩

theorem minLive {N : Nat} (C : Circuit) (fan : FanInTwo C) (f : (Fin N→Bool)→Bool)
    (rep : ∀x,C.eval (List.ofFn x)=f x) (nc : ¬∃v,∀x,f x=v) :
    ∃E : Circuit,(∀g∈E.gates,Good False g) ∧ ReadsBack N E ∧ listed bin E.gates≤listed bin C.gates ∧
      (∀x,E.eval (List.ofFn x)=f x) ∧
      (∀ i : Fin E.gates.length,N+i.val≠E.output → ∃j : Fin E.gates.length,i<j ∧ reads (E.gates.get j) (N+i.val)) ∧
      ∀D : Circuit,FanInTwo D → (∀x,D.eval (List.ofFn x)=f x) → listed bin E.gates≤listed bin D.gates := by
  classical
  let possible:=fun s : Nat=>∃D : Circuit,FanInTwo D ∧ (∀x,D.eval (List.ofFn x)=f x) ∧ listed bin D.gates ≤ s
  have ex : ∃s,possible s:=⟨_,C,fan,rep,le_rfl⟩
  obtain ⟨D,dg,df,ds⟩:=Nat.find_spec ex
  obtain ⟨E,good,back,cost,ef,live⟩:=initial D dg f df nc
  have best (A : Circuit) (ag : FanInTwo A) (af : ∀x,A.eval (List.ofFn x)=f x) : listed bin E.gates≤listed bin A.gates :=
    (cost bin).trans (ds.trans (Nat.find_min' ex ⟨A,ag,af,le_rfl⟩))
  exact ⟨E,good,back,best C fan rep,ef,live,best⟩

theorem bottomStep {n : Nat} (E : Circuit) (good : ∀g∈E.gates,Good False g) (back : ReadsBack (n+1) E)
    (live : ∀i : Fin E.gates.length,n+1+i.val≠E.output → ∃j : Fin E.gates.length,i<j ∧ reads (E.gates.get j) (n+1+i.val))
    (size : 2≤n+1) (ok : E.output<n+1+E.size)
    (sens : ∀i : Fin (n+1),∀x : Fin (n+1)→Bool,V E (Function.update x i (!x i)) E.output ≠V E x E.output)
    (varies : ∀i b,¬∃v,∀y : Fin n→Bool,V E (Fin.insertNth i b y) E.output=v)
    (minimal : ∀D : Circuit,FanInTwo D → (∀x : Fin (n+1)→Bool,D.eval (List.ofFn x)=E.eval (List.ofFn x)) → listed bin E.gates≤listed bin D.gates) :
    ∃(i : Fin (n+1)) (b : Bool) (D : Circuit),FanInTwo D ∧ listed bin D.gates+3≤listed bin E.gates ∧
      ∀y : Fin n→Bool,D.eval (List.ofFn y)=E.eval (List.ofFn (Fin.insertNth i b y)) := by
  classical
  let N:=n+1
  have off:=outputNotRaw good back size ok sens
  have ex : ∃j,j<E.size ∧ (gateAt E j).op≠.not := by
    rcases roots good back E.output ok with h|⟨j,idx,binary,_⟩
    · exact False.elim (off ⟨_,h⟩ rfl)
    · exact ⟨j,idx,binary⟩
  let j:=Nat.find ex
  obtain ⟨hj,nb⟩:=Nat.find_spec ex
  change j<E.size at hj
  change (gateAt E j).op≠.not at nb
  obtain ⟨op,a,b,_,pins⟩:=binaryPins (N:=N) good j hj nb
  have av : a∈(gateAt E j).inputs:=by simp [pins]
  have bv : b∈(gateAt E j).inputs:=by simp [pins]
  have below (w) (mem : w∈(gateAt E j).inputs) : (trace N E w).1<N := by
    have low:=back j hj w mem
    rcases roots good back w (by omega) with h|⟨l,idx,nb,root⟩
    · exact h
    · have h : j≤l:=Nat.find_min' ex ⟨idx,nb⟩
      have first:=Lit.below N E w
      change (trace N E w).1=N+l at root
      change w<N+j at low;omega
  let i : Fin N:=⟨_,below a av⟩
  let k : Fin N:=⟨_,below b bv⟩
  by_cases same : i=k
  · have sa (x : Fin N→Bool) : V E x a=applySign (trace N E a).2 (x i):=literalV good back x a (by have h:=back j hj a av;omega) i rfl
    have sb (x : Fin N→Bool) : V E x b=applySign (trace N E b).2 (x i):=literalV good back x b (by have h:=back j hj b bv;omega) i (congrArg Fin.val same).symm
    have eval (x : Fin N→Bool) : V E x (N+j)=(gateAt E j).op.eval [V E x a,V E x b] := by
      simpa only [pins,List.map_cons,List.map_nil] using gv N E back (List.ofFn x) List.length_ofFn j hj
    have collapse : collapses (fun x : Fin N→Bool=>V E x) (N+j) (fun x=>V E x (N+j)) := by
      by_cases signs : (trace N E a).2=(trace N E b).2
      · refine Or.inr ⟨a,back j hj a av,fun x=>?_⟩
        change V E x (N+j)=V E x a
        rw [eval x,sa x,sb x,signs];rcases op with h|h <;> simp [h,GateOp.eval]
      · rcases op with h|h
        · refine Or.inl ⟨false,fun x=>?_⟩
          change V E x (N+j)=false
          rw [eval x,sa x,sb x,h];cases ha : (trace N E a).2 <;> cases hb : (trace N E b).2 <;> cases x i <;> simp_all [GateOp.eval,applySign]
        · refine Or.inl ⟨true,fun x=>?_⟩
          change V E x (N+j)=true
          rw [eval x,sa x,sb x,h];cases ha : (trace N E a).2 <;> cases hb : (trace N E b).2 <;> cases x i <;> simp_all [GateOp.eval,applySign]
    have nc : ¬∃v,∀x : Fin N→Bool,E.eval (List.ofFn x)=v := by
      rintro ⟨v,val⟩;let x : Fin N→Bool:=fun _=>false
      exact sens i x ((val _).trans (val x).symm)
    obtain ⟨D,fan,z,sem⟩:=folded N N E (good_fan good) (fun x : Fin N→Bool=>List.ofFn x) List.ofFn
      (fun _=>List.length_ofFn) (fun _=>List.length_ofFn) (fun w hw=>Or.inr ⟨w,hw,fun _=>rfl⟩) nc {j}
      (by simpa using And.intro hj nb) (by intro l hl;obtain rfl : l=j:=Finset.mem_singleton.mp hl;exact collapse)
    have m:=minimal D fan sem;rw [Finset.card_singleton] at z;omega
  · obtain ⟨r,ri,diff,rb,second⟩:=another good back i k same j b hj nb bv rfl ok (off i) (sens i)
    have least : j≤r:=Nat.find_min' ex ⟨ri,rb⟩
    exact ⟨i,triple good back live i j r (by omega) ri nb rb ⟨a,av,rfl⟩ second ok (varies i)⟩
end PEqualNP.Outside.L_clb_127.X25689.Lit

namespace PEqualNP.Outside.L_clb_127.X25689.Lit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical

def par (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)

theorem par_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.snoc y b) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  generalize (∑ i : Fin n, if y i = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]

theorem par_insertNth (n : ℕ) (i : Fin (n + 1)) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.insertNth i b y : Fin (n + 1) → Bool) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  generalize (∑ k : Fin n, if y k = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]

theorem par_flip (n : ℕ) (i : Fin (n + 1)) (u : Fin (n + 1) → Bool) :
    par (n + 1) (Function.update u i (!u i)) = !par (n + 1) u := by
  have key : ∀ (x : Bool) (p : Fin n → Bool),
      par (n + 1) (Function.update (Fin.insertNth i x p : Fin (n + 1) → Bool) i (!x))
        = !par (n + 1) (Fin.insertNth i x p : Fin (n + 1) → Bool) := by
    intro x p
    rw [Fin.update_insertNth, par_insertNth, par_insertNth]
    cases par n p <;> cases x <;> rfl
  have := key (u i) (Fin.removeNth i u)
  rw [Fin.insertNth_self_removeNth] at this
  exact this

theorem parNC (n : Nat) (c : Bool) : ¬∃v,∀x : Fin (n+1)→Bool,xor (par (n+1) x) c=v := by
  rintro ⟨v,h⟩
  let u : Fin n→Bool:=fun _=>false
  have eq:=(h (Fin.snoc u false)).trans (h (Fin.snoc u true)).symm
  rw [par_snoc,par_snoc] at eq;cases bit : par n u <;> cases c <;> simp [bit] at eq

theorem parityBinary : ∀n c (C : Circuit),FanInTwo C →
    (∀x : Fin (n+1)→Bool,C.eval (List.ofFn x)=xor (par (n+1) x) c) →
    3*n≤listed bin C.gates := by
  intro n
  induction n with
  | zero => intro c C _ _;simp
  | succ n ih =>
    intro c C fan sem
    let N:=n+1+1
    let f:=fun x : Fin N→Bool=>xor (par N x) c
    obtain ⟨E,good,back,cost,eq,live,minimal⟩:=minLive C fan f sem (parNC (n+1) c)
    have nc : ¬∃v,∀x : Fin N→Bool,E.eval (List.ofFn x)=v :=
      fun ⟨v,h⟩=>parNC (n+1) c ⟨v,fun x=>(eq x).symm.trans (h x)⟩
    have depends (i : Fin N) (x : Fin N→Bool) : V E (Function.update x i (!x i)) E.output≠V E x E.output := by
      change E.eval (List.ofFn _ )≠E.eval (List.ofFn x)
      rw [eq,eq];unfold f;rw [par_flip];cases par N x <;> cases c <;> decide
    have restricted (i : Fin N) (b : Bool) : ¬∃v,∀y : Fin (n+1)→Bool,V E (Fin.insertNth i b y) E.output=v := by
      rintro ⟨v,h⟩
      apply parNC n (xor b c)
      refine ⟨v,fun y=>?_⟩
      have z:=h y
      change E.eval (List.ofFn (Fin.insertNth i b y))=v at z
      rw [eq] at z;unfold f at z;rwa [par_insertNth,Bool.xor_assoc] at z
    obtain ⟨i,b,D,fanD,saved,values⟩:=bottomStep E good back live (by omega) (outputBound E nc) depends restricted
      (fun D g sem=>minimal D g (fun x=>(sem x).trans (eq x)))
    have next (y : Fin (n+1)→Bool) : D.eval (List.ofFn y)=xor (par (n+1) y) (xor b c) := by
      rw [values,eq];unfold f;rw [par_insertNth,Bool.xor_assoc]
    have floor:=ih (xor b c) D fanD next
    omega
end PEqualNP.Outside.L_clb_127.X25689.Lit

namespace PEqualNP.Outside.L_clb_127.X25689.Lit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical

theorem parBit (n : Nat) (x : Fin n→Bool) :
    ((Finset.univ.filter fun i : Fin n=>x i).card).testBit 0=par n x := by
  simp [par,Nat.testBit_zero]

theorem flipBit {m : Nat} (j : Fin m) (x : Fin m→Bool) :
    par m (Function.update x j (!x j)) = !par m x := by
  cases m with
  | zero => exact j.elim0
  | succ m => exact par_flip m j x

theorem allBlockEss {n m : Nat} (owner : Fin n→Fin m) (block : Fin m→(Fin n→Bool)→Bool)
    (localRead : ∀j x y,(∀i,owner i=j → x i=y i) → block j x=block j y)
    (pos : ∀i,∃x,block (owner i) (Function.update x i false)=false ∧ block (owner i) (Function.update x i true)=true) :
    let f:=fun x=>par m (fun j=>block j x)
    ∀i,∃x,f (Function.update x i false)≠f (Function.update x i true) := by
  dsimp only
  intro i
  obtain ⟨x,zero,one⟩:=pos i
  let lo:=fun j=>block j (Function.update x i false)
  let hi:=fun j=>block j (Function.update x i true)
  have flip : hi=Function.update lo (owner i) (!(lo (owner i))) := by
    funext j;by_cases self : j=owner i
    · subst j;simp [hi,lo,zero,one]
    · rw [Function.update_of_ne self]
      apply localRead
      intro v hv
      have ne : v≠i:=fun e=>self (hv ▸ congrArg owner e)
      simp [Function.update_of_ne ne]
  refine ⟨x,?_⟩
  change par m lo ≠ par m hi
  rw [flip,flipBit];cases par m lo <;> decide

theorem face {n m : Nat} (owner : Fin n→Fin m) (block : Fin m→(Fin n→Bool)→Bool) (surj : Function.Surjective owner)
    (localRead : ∀j x y,(∀i,owner i=j → x i=y i) → block j x=block j y)
    (pos : ∀i,∃x,block (owner i) (Function.update x i false)=false ∧ block (owner i) (Function.update x i true)=true) :
    ∃ wire : Fin m→Fin n, ∃fixed : Fin n→Bool, Function.Injective wire ∧
      ∀j y,block j (plug wire fixed y)=y j := by
  classical
  let wire:=fun j=>(surj j).choose
  have section' (j) : owner (wire j)=j:=(surj j).choose_spec
  have inj : Function.Injective wire:=fun a b h=>(section' a).symm.trans ((congrArg owner h).trans (section' b))
  let witness:=fun j=>(pos (wire j)).choose
  let fixed:=fun i=>witness (owner i) i
  refine ⟨wire,fixed,inj,fun j y=>?_⟩
  have many : block j (plug wire fixed y) = block j (Function.update (witness j) (wire j) (y j)) := by
    apply localRead
    intro i member
    by_cases eq : i=wire j
    · subst i;rw [onWire wire fixed inj,Function.update_self]
    · have out : i∉Finset.univ.image wire := by
        intro h;obtain ⟨t,_,hit⟩:=Finset.mem_image.mp h
        have e : t=j:=(section' t).symm.trans ((congrArg owner hit).trans member)
        exact eq (hit.symm.trans (congrArg wire e))
      simp [plug,out,Function.update_of_ne eq,fixed,member]
  have h:=(pos (wire j)).choose_spec
  change block (owner (wire j)) (Function.update (witness j) (wire j) false)=false ∧
    block (owner (wire j)) (Function.update (witness j) (wire j) true)=true at h
  rw [section' j] at h
  rw [many];cases value : y j <;> first | exact h.1 | exact h.2

theorem allLower {n m : Nat} (mp : 0 < m) (owner : Fin n→Fin m) (block : Fin m→(Fin n→Bool)→Bool)
    (surj : Function.Surjective owner) (localRead : ∀j x y,(∀i,owner i=j → x i=y i) → block j x=block j y)
    (pos : ∀i,∃x,block (owner i) (Function.update x i false)=false ∧ block (owner i) (Function.update x i true)=true)
    (C : Circuit) (fan : FanInTwo C) (rep : ∀x,C.eval (List.ofFn x)=par m (fun j=>block j x)) :
    n-m+3*(m-1)≤listed bin C.gates ∧ n-m+4*(m-1)≤C.size := by
  classical
  obtain ⟨wire,fixed,inj,equals⟩:=face owner block surj localRead pos
  let f:=fun x=>par m (fun j=>block j x)
  have parEq (x : Fin m→Bool) : f (plug wire fixed x)=par m x:=congrArg (par m) (funext (fun j=>equals j x))
  have non : ∃a b : Fin m→Bool,f (plug wire fixed a)≠f (plug wire fixed b) := by
    let i : Fin m:=⟨0,mp⟩
    let a : Fin m→Bool:=fun _=>false
    refine ⟨Function.update a i (!a i),a,?_⟩
    rw [parEq,parEq,flipBit];cases par m a <;> decide
  obtain ⟨D,dFan,cost,invert,answer⟩:=restrict C fan wire fixed inj f rep non
  have all:=allBlockEss owner block localRead pos
  have all' : ((Finset.univ : Finset (Fin n)).filter (fun i=>∃x,f (Function.update x i false)≠f (Function.update x i true)))=Finset.univ := by
    ext i;simp only [Finset.mem_filter,Finset.mem_univ,true_and,iff_true];exact all i
  rw [all',Finset.card_univ,Fintype.card_fin] at cost
  have lower : 3*(m-1)≤listed bin D.gates := by
    cases m with
    | zero => simp
    | succ k =>
      have z:=parityBinary k false D dFan (fun x=>by rw [answer,parEq];simp)
      simpa using z
  have need : 4*(m-1)≤D.size:=PEqualNP.Outside.L_clb_127.X25689.OldParity.parity_lower4 m D.size
    ⟨D,dFan,le_rfl,fun x=>(answer x).trans (parEq x)⟩
  have sums (E : Circuit) : listed bin E.gates+listed inv E.gates=E.size := by
    obtain ⟨a,b⟩:=costs E
    rw [a,b];apply Nat.sub_add_cancel
    exact List.length_filter_le _ _
  have le : m≤n:=by simpa using Fintype.card_le_of_injective wire inj
  have d:=sums D;have c:=sums C;omega
end PEqualNP.Outside.L_clb_127.X25689.Lit

namespace PEqualNP.Outside.L_clb_127.X25689.Lit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical

private theorem wires_append (gs hs : List Gate) (out : ℕ) (x : List Bool) :
    (⟨gs ++ hs, out⟩ : Circuit).wires x =
      hs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        ((⟨gs, 0⟩ : Circuit).wires x) := by
  simp [Circuit.wires, List.foldl_append]

private theorem wires_length (gs : List Gate) (out : ℕ) (x : List Bool) :
    ((⟨gs, out⟩ : Circuit).wires x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp [Circuit.wires, List.foldl_append] at ih ⊢
    omega

private theorem wires_getD_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs.length) :
    ((⟨gs ++ hs, 0⟩ : Circuit).wires x).getD i false =
      ((⟨gs, 0⟩ : Circuit).wires x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    have hlen : i < ((⟨gs ++ hs, 0⟩ : Circuit).wires x).length := by
      rw [wires_length, List.length_append]; omega
    rw [← List.append_assoc, wires_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen, ← List.getD_eq_getElem?_getD]
    exact ih

private theorem map_gates_sim (L1 M : ℕ) (ρ : ℕ → ℕ) (gs : List Gate) (x W2 : List Bool)
    (hxlen : x.length = L1)
    (hM : W2.length + gs.length ≤ M)
    (hρ_in : ∀ i < L1, (ρ i < W2.length ∧ W2.getD (ρ i) false = x.getD i false) ∨
                       (M ≤ ρ i ∧ x.getD i false = false))
    (hρ_ge : ∀ i, L1 ≤ i → ρ i = i - L1 + W2.length) :
    ∀ (i : ℕ),
      ((⟨gs.map (fun g => ⟨g.op, g.inputs.map ρ⟩), 0⟩ : Circuit).wires W2).getD (ρ i) false =
        ((⟨gs, 0⟩ : Circuit).wires x).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i
    simp only [List.map_nil, Circuit.wires, List.foldl_nil]
    by_cases hi : i < L1
    · rcases hρ_in i hi with ⟨_, heq⟩ | ⟨hge, hfalse⟩
      · exact heq
      · have : W2.length ≤ ρ i := by simp at hM; omega
        rw [hfalse, List.getD_eq_getElem?_getD, List.getElem?_eq_none this]; rfl
    · have h1 : L1 ≤ i := by omega
      have h2 : W2.length ≤ ρ i := by rw [hρ_ge i h1]; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : x.length ≤ i),
        List.getElem?_eq_none h2]
  | append_singleton gs g ih =>
    intro i
    have hM' : W2.length + gs.length ≤ M := by simp at hM; omega
    have ih' := ih hM'
    set gs' : List Gate := gs.map (fun g => ⟨g.op, g.inputs.map ρ⟩)
    set g' : Gate := ⟨g.op, g.inputs.map ρ⟩
    have hmap : (gs ++ [g]).map (fun g => ⟨g.op, g.inputs.map ρ⟩) = gs' ++ [g'] := by
      simp [gs', g']
    rw [hmap, wires_append, wires_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set W1 := (⟨gs, 0⟩ : Circuit).wires x
    set W2' := (⟨gs', 0⟩ : Circuit).wires W2
    have hW1len : W1.length = L1 + gs.length := by rw [wires_length, hxlen]
    have hW2'len : W2'.length = W2.length + gs.length := by
      rw [wires_length]; simp [gs']
    have hval_eq : g'.op.eval (g'.inputs.map fun k => W2'.getD k false) =
        g.op.eval (g.inputs.map fun k => W1.getD k false) := by
      simp only [g', List.map_map]
      congr 1
      apply List.map_congr_left
      intro k _
      exact ih' k
    rw [hval_eq]
    by_cases hi_lt : i < L1 + gs.length
    · by_cases h1 : i < L1
      · rcases hρ_in i h1 with ⟨hρlt, _⟩ | ⟨hρge, hfalse⟩
        · have hL : ∀ (l : List Bool) (a : Bool) (k : ℕ), k < l.length →
              (l ++ [a]).getD k false = l.getD k false := by
            intro l a k hk
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hk, ← List.getD_eq_getElem?_getD]
          rw [hL W2' _ (ρ i) (by omega), hL W1 _ i (by omega)]
          exact ih' i
        · have hW2_ge : (W2' ++ [g.op.eval (g.inputs.map fun k => W1.getD k false)]).length ≤ ρ i := by
            simp only [List.length_append, List.length_singleton, hW2'len]
            simp at hM; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hW2_ge]
          simp only [Option.getD_none]
          have hW1_get : (W1 ++ [g.op.eval (g.inputs.map fun k => W1.getD k false)]).getD i false = x.getD i false := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < W1.length),
              ← List.getD_eq_getElem?_getD]
            have hpre := wires_getD_prefix [] gs x i (by simpa [hxlen] using h1)
            simpa [W1, Circuit.wires] using hpre
          rw [hW1_get, hfalse]
      · have hρi_lt : ρ i < W2'.length := by rw [hρ_ge i (by omega)]; omega
        have hL : ∀ (l : List Bool) (a : Bool) (k : ℕ), k < l.length →
            (l ++ [a]).getD k false = l.getD k false := by
          intro l a k hk
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hk, ← List.getD_eq_getElem?_getD]
        rw [hL W2' _ (ρ i) hρi_lt, hL W1 _ i (by omega)]
        exact ih' i
    · by_cases hi_eq : i = L1 + gs.length
      · subst hi_eq
        have hρi_eq : ρ (L1 + gs.length) = W2'.length := by
          rw [hρ_ge _ (by omega)]; omega
        rw [hρi_eq, ← hW1len]
        simp [List.getD_eq_getElem?_getD]
      · have hρi_gt : W2'.length + 1 ≤ ρ i := by
          rw [hρ_ge i (by omega)]; omega
        simp [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simp [hW1len]; omega : (W1 ++ [_]).length ≤ i),
          List.getElem?_eq_none (by simp [hW2'len]; omega : (W2' ++ [_]).length ≤ ρ i)]

theorem xorStepAlt (v : List Bool) (i j : ℕ) (hi : i < v.length) (hj : j < v.length) :
    (Normalize.run [⟨GateOp.or, [i, j]⟩, ⟨GateOp.and, [i, j]⟩, ⟨GateOp.not, [v.length + 1]⟩,
      ⟨GateOp.and, [v.length, v.length + 2]⟩] v).getD (v.length + 3) false
      = xor (v.getD i false) (v.getD j false) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [Normalize.run, GateOp.eval, A _ _ hi, A _ _ hj]
  cases v[i]?.getD false <;> cases v[j]?.getD false <;> rfl

theorem listMono (gs : List Gate) (mono : ∀g∈gs,g.op=.and ∨ g.op=.or) : listed bin gs=gs.length := by
  induction gs with
  | nil => simp [listed]
  | cons g l ih =>
    have ok:=mono g List.mem_cons_self
    have h:=ih (fun a ha=>mono a (List.mem_cons_of_mem _ ha))
    rcases ok with e|e <;> simp [listed,bin,e] at h ⊢ <;> omega

def appendShift (N k i : Nat) := if i<N then i else i+k
def translated (N k : Nat) (g : Gate) : Gate:=⟨g.op,g.inputs.map (appendShift N k)⟩
def filler : Gate:=⟨.or,[0,0]⟩

theorem appendBlock {n : Nat} (gs : List Gate) (P : Circuit) (mono : Monotone2 P)
    (budget : Nat) (cost : P.size≤budget) (out : P.output<n+P.size) :
    ∃hs : List Gate, ∃w : Nat, hs.length=budget ∧ listed bin hs=budget ∧
      (∀g∈hs,g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) ∧
      w<n+(gs++hs).length ∧ ∀x : Fin n→Bool,(run (gs++hs) (List.ofFn x)).getD w false=P.eval (List.ofFn x) := by
  let ρ:=appendShift n gs.length
  let translatedP:=P.gates.map (translated n gs.length)
  let padding:=List.replicate (budget-P.size) filler
  let hs:=translatedP++padding
  have hlen : hs.length=budget:=by simp [hs,translatedP,padding,Circuit.size] at cost ⊢;omega
  have mono' (g) (hg : g∈hs) : (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by
    rcases List.mem_append.mp hg with h|h
    · obtain ⟨q,mem,rfl⟩:=List.mem_map.mp h
      obtain ⟨op,l⟩:=mono q mem
      exact ⟨by simpa [translated] using op,by simpa [translated] using l⟩
    · have e : g=filler:=(List.mem_replicate.mp h).2
      subst g;exact ⟨Or.inr rfl,by decide⟩
  have bound : ρ P.output<n+gs.length+translatedP.length := by
    simp only [translatedP,List.length_map];unfold ρ appendShift;split <;> change P.output<n+P.gates.length at out <;> omega
  refine ⟨hs,ρ P.output,hlen,(listMono _ (fun g h=>(mono' g h).1)).trans hlen,?_,?_,?_⟩
  · intro g h;obtain ⟨op,l⟩:=mono' g h;exact ⟨by rcases op with eq|eq <;> simp [eq],l⟩
  · change ρ P.output<n+(gs++(translatedP++padding)).length
    rw [List.length_append,List.length_append];omega
  · intro x
    let X:=List.ofFn x
    let W:=run gs X
    have lx : X.length=n:=List.length_ofFn
    have lw : W.length=n+gs.length:=by rw [show W.length=X.length+gs.length from run_length gs X,lx]
    have z:=map_gates_sim n (W.length+P.gates.length) ρ P.gates X W lx le_rfl
      (fun i hi=>Or.inl ⟨by simp [ρ,appendShift,hi,lw];omega,by simp [ρ,appendShift,hi,W];exact run_input _ _ _ (by rwa [lx])⟩)
      (fun i hi=>by simp [ρ,appendShift,show ¬i<n by omega,lw];omega) P.output
    change (run (gs++(translatedP++padding)) X).getD (ρ P.output) false=_
    rw [←List.append_assoc,run_init _ _ _ _ (by simp [lx];omega)]
    exact (show (run (gs++translatedP) X).getD (ρ P.output) false=(run translatedP W).getD (ρ P.output) false from by
      simp [run,W,List.foldl_append]).trans z

def xorList (m a b : Nat) : List Gate:=[⟨.or,[a,b]⟩,⟨.and,[a,b]⟩,⟨.not,[m+1]⟩,⟨.and,[m,m+2]⟩]
theorem xorCost (m a b : Nat) : (xorList m a b).length=4 ∧ listed bin (xorList m a b)=3 ∧
    ∀g∈xorList m a b,g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2 := by
  refine ⟨rfl,by simp [xorList,listed,bin],?_⟩
  intro g hg;simp only [xorList,List.mem_cons,List.mem_nil_iff,or_false] at hg
  rcases hg with e|e|e|e <;> subst g <;> simp

theorem xorAt {n : Nat} (gs : List Gate) (a b : Nat) (ha : a<n+gs.length) (hb : b<n+gs.length)
    (x : Fin n→Bool) : (run (gs++xorList (n+gs.length) a b) (List.ofFn x)).getD (n+gs.length+3) false=
      xor ((run gs (List.ofFn x)).getD a false) ((run gs (List.ofFn x)).getD b false) := by
  let W:=run gs (List.ofFn x)
  have len : W.length=n+gs.length:=by simp [W,run_length]
  have h:=xorStepAlt W a b (by omega) (by omega)
  rw [len] at h
  change (run (xorList (n+gs.length) a b) W).getD (n+gs.length+3) false=_ at h
  exact (show run (gs++xorList (n+gs.length) a b) (List.ofFn x)=run (xorList (n+gs.length) a b) W from by
    simp [run,W,List.foldl_append]) ▸ h
end PEqualNP.Outside.L_clb_127.X25689.Lit

namespace PEqualNP.Outside.L_clb_127.X25689.Lit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical

def oddCount {m : Nat} (S : Finset (Fin m)) (x : Fin m→Bool) := decide ((S.filter (fun j=>x j)).card % 2=1)

theorem oddInsert {m : Nat} (S : Finset (Fin m)) (j : Fin m) (off : j∉S) (x : Fin m→Bool) :
    oddCount (insert j S) x=xor (oddCount S x) (x j) := by
  have notin : j∉S.filter (fun j=>x j):=fun h=>off (Finset.mem_filter.mp h).1
  cases v : x j <;> unfold oddCount <;> simp [Finset.filter_insert,v,notin,Nat.add_mod]
  have h:=Nat.mod_two_eq_zero_or_one (S.filter (fun i=>x i)).card
  rcases h with e|e <;> simp [e]

def allowed (g : Gate) := g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2

theorem buildParts {n m : Nat} (block : Fin m→(Fin n→Bool)→Bool) (cap : Fin m→Nat)
    (supply : ∀j,∃P : Circuit,Monotone2 P ∧ P.size≤cap j ∧ P.output<n+P.size ∧ ∀x,P.eval (List.ofFn x)=block j x)
    (S : Finset (Fin m)) (non : S.Nonempty) :
    ∃ (gs : List Gate) (w : Nat), (∀g∈gs,allowed g) ∧
      gs.length=(∑j∈S,cap j)+4*(S.card-1) ∧ listed bin gs=(∑j∈S,cap j)+3*(S.card-1) ∧
      w<n+gs.length ∧ ∀x : Fin n→Bool,(run gs (List.ofFn x)).getD w false=oddCount S (fun j=>block j x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at non
  | @insert j S off ih =>
    obtain ⟨P,mono,cost,out,value⟩:=supply j
    by_cases empty : S=∅
    · subst S
      obtain ⟨hs,w,len,charge,fan,bound,eval⟩:=appendBlock [] P mono (cap j) cost out
      refine ⟨hs,w,fan,by simpa using len,by simpa using charge,by simpa using bound,fun x=>?_⟩
      have e : (run hs (List.ofFn x)).getD w false=block j x:=by simpa using (eval x).trans (value x)
      rw [e,oddInsert _ _ (by simp)]
      simp [oddCount]
    · obtain ⟨gs,a,ok,len,charge,low,eval⟩:=ih (Finset.nonempty_iff_ne_empty.mpr empty)
      obtain ⟨hs,b,hLen,hCost,hFan,hBound,hEval⟩:=appendBlock gs P mono (cap j) cost out
      let t:=n+(gs++hs).length
      let gates:=xorList t a b
      obtain ⟨xLen,xCost,xFan⟩:=xorCost t a b
      have positive:=Finset.card_pos.mp (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty))
      have card : 0<S.card:=Finset.card_pos.mpr positive
      refine ⟨(gs++hs)++gates,t+3,?_,?_,?_,?_,fun x=>?_⟩
      · intro g h
        rcases List.mem_append.mp h with earlier|last
        · rcases List.mem_append.mp earlier with h|h
          · exact ok g h
          · exact hFan g h
        · exact xFan g last
      · simp only [List.length_append,Finset.sum_insert off,Finset.card_insert_of_notMem off]
        change gs.length+hs.length+(xorList t a b).length=_
        rw [xLen,hLen,len];omega
      · have append (l r : List Gate) : listed bin (l++r)=listed bin l+listed bin r:=by simp [listed]
        rw [append,append,charge,hCost,show listed bin gates=3 from xCost,Finset.sum_insert off,Finset.card_insert_of_notMem off];omega
      · simp [gates,xorList,t] <;> omega
      · have al : a<n+(gs++hs).length:=by simp;omega
        have e:=xorAt (gs++hs) a b al hBound x
        have orig : (run (gs++hs) (List.ofFn x)).getD a false=oddCount S (fun j=>block j x) :=
          (run_init gs hs _ a (by simpa using low)).trans (eval x)
        change (run ((gs++hs)++xorList t a b) (List.ofFn x)).getD (t+3) false = _
        rw [e,orig,hEval,value,oddInsert S j off]

theorem allUpper {n m : Nat} (mp : 0 < m) (owner : Fin n→Fin m) (block : Fin m→(Fin n→Bool)→Bool)
    (surj : Function.Surjective owner)
    (pos : ∀i,∃x,block (owner i) (Function.update x i false)=false ∧ block (owner i) (Function.update x i true)=true)
    (small : ∀ j,∃P : Circuit,Monotone2 P ∧ P.size+1≤((Finset.univ : Finset (Fin n)).filter (fun i=>owner i=j)).card ∧
      ∀x,P.eval (List.ofFn x)=block j x) :
    ∃C : Circuit,FanInTwo C ∧ (∀x,C.eval (List.ofFn x)=par m (fun j=>block j x)) ∧
      listed bin C.gates=n-m+3*(m-1) ∧ C.size=n-m+4*(m-1) := by
  classical
  let fib:=fun j=>(Finset.univ : Finset (Fin n)).filter (fun i=>owner i=j)
  let cap:=fun j=>(fib j).card-1
  have one (j : Fin m) : 1≤(fib j).card:=by
    obtain ⟨i,eq⟩:=surj j
    exact Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq⟩⟩
  have total : (∑j : Fin m,(fib j).card)=n := by
    simp only [fib,Finset.card_filter];rw [Finset.sum_comm]
    simp
  have exactCost : (∑j : Fin m,cap j)=n-m := by
    have sums : (∑j : Fin m,(cap j+1))=n:=by
      rw [←total];apply Finset.sum_congr rfl;intro j _
      dsimp [cap];have :=one j;omega
    rw [Finset.sum_add_distrib] at sums;simp at sums;omega
  have supply (j : Fin m) : ∃P : Circuit,Monotone2 P ∧ P.size≤cap j ∧ P.output<n+P.size ∧ ∀x,P.eval (List.ofFn x)=block j x := by
    obtain ⟨P,mon,size,sim⟩:=small j
    change P.size+1≤(fib j).card at size
    obtain ⟨i,e⟩:=surj j
    obtain ⟨x,l,r⟩:=pos i;rw [e] at l r
    have nc : ¬∃v,∀x : Fin n→Bool,P.eval (List.ofFn x)=v := by
      rintro ⟨v,z⟩
      have left:=(sim (Function.update x i false)).symm.trans (z _)
      have right:=(sim (Function.update x i true)).symm.trans (z _)
      rw [l] at left;rw [r] at right;cases v <;> contradiction
    exact ⟨P,mon,by dsimp [cap];omega,outputBound P nc,sim⟩
  have non : (Finset.univ : Finset (Fin m)).Nonempty:=⟨⟨0,mp⟩,Finset.mem_univ _⟩
  obtain ⟨gs,w,fan,len,charge,_,eval⟩:=buildParts block cap supply Finset.univ non
  exact ⟨⟨gs,w⟩,fan,eval,by simpa [exactCost] using charge,by simpa [Circuit.size,exactCost] using len⟩
end PEqualNP.Outside.L_clb_127.X25689.Lit

namespace PEqualNP.Outside.L_clb_127
open PEqualNP.Outside.L_clb_127.X25689 in
theorem T25689 : ∀ (n m : Nat), 0 < m →
  let inv := fun (G : PEqualNP.CircuitLowerBounds.Circuit) =>
    (G.gates.filter (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length
  let binary := fun (G : PEqualNP.CircuitLowerBounds.Circuit) => G.size - inv G
  ∀ (owner : Fin n → Fin m) (block : Fin m → (Fin n → Bool) → Bool),
    Function.Surjective owner →
    (∀ j x y, (∀ i, owner i = j → x i = y i) → block j x = block j y) →
    (∀ i, ∃ x : Fin n → Bool, block (owner i) (Function.update x i false) = false ∧
        block (owner i) (Function.update x i true) = true) →
    (∀ j, ∃ P : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 P ∧
      P.size + 1 ≤ ((Finset.univ : Finset (Fin n)).filter (fun i => owner i = j)).card ∧
      ∀ x, P.eval (List.ofFn x) = block j x) →
    let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      PEqualNP.MetaComplexity.FanInTwo C ∧ ∀ x : Fin n → Bool,
        C.eval (List.ofFn x) = (((Finset.univ : Finset (Fin m)).filter (fun j => block j x)).card).testBit 0
    let B := (n-m)+3*(m-1)
    let G := (n-m)+4*(m-1)
    (∃ C, fits C ∧ binary C = B ∧ C.size = G) ∧ (∀ C, fits C → B ≤ binary C ∧ G ≤ C.size) := by
  intro n m mp
  dsimp only
  intro owner block surj localRead pos small
  obtain ⟨C,fan,eval,bin,len⟩:=Lit.allUpper mp owner block surj pos small
  constructor
  · refine ⟨C,⟨fan,fun x=>(eval x).trans (Lit.parBit _ _).symm⟩,?_,len⟩
    rwa [(costs C).2] at bin
  · intro E h
    obtain ⟨binary,total⟩:=Lit.allLower mp owner block surj localRead pos E h.1 (fun x=>(h.2 x).trans (Lit.parBit _ _))
    rw [(costs E).2] at binary
    exact ⟨binary,total⟩

end PEqualNP.Outside.L_clb_127

namespace PEqualNP.Outside.L_clb_127.C120

def loc (n : Nat) (hn : 0 < n) (k : Nat) : Fin n := ⟨k % n, Nat.mod_lt _ hn⟩

def cnt (n w : Nat) (hn : 0 < n) (tab : Fin n × (Fin (w+1) → Bool) → Bool) : Nat :=
  ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
    ∀ i : Fin n, tab (i, fun j => x (loc n hn (i.val+j.val))) = true)).card

def fval (n w : Nat) (hn : 0 < n) (raw : Fin (n*2^(w+1)) → Bool) : Bool :=
  (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => ∀ i : Fin n,
    (List.ofFn raw).getD (i.val*2^(w+1) +
      ∑ j : Fin (w+1), if x (loc n hn (i.val+j.val)) then 2^j.val else 0) false = true)).card).testBit 0

def pval (w : Nat) (p : Fin (w+1) → Bool) : Nat := ∑ j : Fin (w+1), if p j then 2^j.val else 0

lemma ha_bsum_lt (k : Nat) (p : Fin k → Bool) :
    (∑ j : Fin k, if p j then 2^j.val else 0) < 2^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    have h1 := ih (fun j => p j.castSucc)
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [pow_succ]
    split_ifs <;> omega

lemma ha_bsum_bit (k : Nat) (p : Fin k → Bool) (i : Nat) :
    (∑ j : Fin k, if p j then 2^j.val else 0).testBit i =
      if h : i < k then p ⟨i, h⟩ else false := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    have h1 := ha_bsum_lt k (fun j => p j.castSucc)
    have h2 := ih (fun j => p j.castSucc)
    simp only [Fin.val_castSucc, Fin.val_last] at h1 h2 ⊢
    have e : (∑ j : Fin k, if p j.castSucc then 2^j.val else 0) +
        (if p (Fin.last k) then 2^k else 0) =
        2^k * (if p (Fin.last k) then 1 else 0) +
          (∑ j : Fin k, if p j.castSucc then 2^j.val else 0) := by
      split_ifs <;> omega
    rw [e, Nat.testBit_two_pow_mul_add _ h1, h2 i]
    by_cases hik : i < k
    · have hik' : i < k+1 := by omega
      rw [if_pos hik, dif_pos hik, dif_pos hik']
      rfl
    · rw [if_neg hik]
      by_cases hik' : i < k+1
      · have hi : i = k := by omega
        subst hi
        rw [dif_pos hik', Nat.sub_self]
        have hl : (⟨i, hik'⟩ : Fin (i+1)) = Fin.last i := rfl
        rw [hl]
        cases p (Fin.last i) <;> simp
      · rw [dif_neg hik']
        have hz : (if p (Fin.last k) then 1 else 0 : Nat).testBit (i - k) = false := by
          apply Nat.testBit_eq_false_of_lt
          have h3 : 2 ≤ 2^(i-k) := by
            calc 2 = 2^1 := by norm_num
              _ ≤ 2^(i-k) := Nat.pow_le_pow_right (by norm_num) (by omega)
          split_ifs <;> omega
        exact hz

lemma ha_bsum_of (k m : Nat) (hm : m < 2^k) :
    (∑ j : Fin k, if m.testBit j.val then 2^j.val else 0) = m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [ha_bsum_bit k (fun j => m.testBit j.val) i]
  by_cases hik : i < k
  · rw [dif_pos hik]
  · rw [dif_neg hik]
    symm
    apply Nat.testBit_eq_false_of_lt
    calc m < 2^k := hm
      _ ≤ 2^i := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma pval_lt (w : Nat) (p : Fin (w+1) → Bool) : pval w p < 2^(w+1) := by
  exact ha_bsum_lt (w+1) p

lemma enc_bound (n w : Nat) (s : Fin n × (Fin (w+1) → Bool)) :
    s.1.val*2^(w+1) + pval w s.2 < n*2^(w+1) := by
  have h1 := pval_lt w s.2
  have h2 : (s.1.val+1)*2^(w+1) ≤ n*2^(w+1) := Nat.mul_le_mul_right _ s.1.isLt
  rw [Nat.add_mul, Nat.one_mul] at h2
  omega

lemma dec_bound (n w : Nat) (idx : Fin (n*2^(w+1))) : idx.val / 2^(w+1) < n := by
  rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by norm_num))]
  exact idx.isLt

def enc (n w : Nat) (s : Fin n × (Fin (w+1) → Bool)) : Fin (n*2^(w+1)) :=
  ⟨s.1.val*2^(w+1) + pval w s.2, enc_bound n w s⟩

def dec (n w : Nat) (idx : Fin (n*2^(w+1))) : Fin n × (Fin (w+1) → Bool) :=
  (⟨idx.val / 2^(w+1), dec_bound n w idx⟩, fun j => (idx.val % 2^(w+1)).testBit j.val)

lemma dec_enc (n w : Nat) (s : Fin n × (Fin (w+1) → Bool)) : dec n w (enc n w s) = s := by
  have hp := pval_lt w s.2
  have hpos : 0 < 2^(w+1) := Nat.pow_pos (by norm_num)
  apply Prod.ext
  · apply Fin.ext
    show (s.1.val*2^(w+1) + pval w s.2) / 2^(w+1) = s.1.val
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hp, Nat.zero_add]
  · funext j
    show ((s.1.val*2^(w+1) + pval w s.2) % 2^(w+1)).testBit j.val = s.2 j
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp]
    have h := ha_bsum_bit (w+1) s.2 j.val
    rw [dif_pos j.isLt] at h
    exact h

lemma enc_dec (n w : Nat) (idx : Fin (n*2^(w+1))) : enc n w (dec n w idx) = idx := by
  have hpos : 0 < 2^(w+1) := Nat.pow_pos (by norm_num)
  apply Fin.ext
  show idx.val / 2^(w+1) * 2^(w+1) + pval w (fun j => (idx.val % 2^(w+1)).testBit j.val) = idx.val
  have h : pval w (fun j => (idx.val % 2^(w+1)).testBit j.val) = idx.val % 2^(w+1) :=
    ha_bsum_of (w+1) _ (Nat.mod_lt _ hpos)
  rw [h]
  exact Nat.div_add_mod' _ _

lemma ha_getD (N : Nat) (raw : Fin N → Bool) (k : Nat) (h : k < N) :
    (List.ofFn raw).getD k false = raw ⟨k, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

lemma fval_tab (n w : Nat) (hn : 0 < n) (tab : Fin n × (Fin (w+1) → Bool) → Bool) :
    fval n w hn (fun idx => tab (dec n w idx)) = (cnt n w hn tab).testBit 0 := by
  unfold fval cnt
  congr 2
  apply Finset.filter_congr
  intro x _
  apply forall_congr'
  intro i
  have hb := enc_bound n w (i, fun j => x (loc n hn (i.val+j.val)))
  have hg := ha_getD _ (fun idx => tab (dec n w idx)) _ hb
  have hd := dec_enc n w (i, fun j => x (loc n hn (i.val+j.val)))
  have he : (⟨i.val*2^(w+1) + pval w (fun j => x (loc n hn (i.val+j.val))), hb⟩ :
      Fin (n*2^(w+1))) = enc n w (i, fun j => x (loc n hn (i.val+j.val))) := rfl
  rw [he] at hg
  simp only [hd] at hg
  have hs : (∑ j : Fin (w+1), if x (loc n hn (i.val+j.val)) then 2^j.val else 0) =
      pval w (fun j => x (loc n hn (i.val+j.val))) := rfl
  rw [hs, hg]

lemma ha_upd (n w : Nat) (tab : Fin n × (Fin (w+1) → Bool) → Bool)
    (s : Fin n × (Fin (w+1) → Bool)) (b : Bool) :
    Function.update (fun idx => tab (dec n w idx)) (enc n w s) b =
      fun idx => (Function.update tab s b) (dec n w idx) := by
  funext idx
  by_cases h : idx = enc n w s
  · subst h
    rw [Function.update_self, dec_enc, Function.update_self]
  · have h2 : dec n w idx ≠ s := by
      intro e
      apply h
      rw [← e, enc_dec]
    rw [Function.update_of_ne h, Function.update_of_ne h2]

lemma dep_mem (n w : Nat) (hn : 0 < n) (tab : Fin n × (Fin (w+1) → Bool) → Bool)
    (s : Fin n × (Fin (w+1) → Bool))
    (h : (cnt n w hn (Function.update tab s false)).testBit 0 ≠
      (cnt n w hn (Function.update tab s true)).testBit 0) :
    ∃ x : Fin (n*2^(w+1)) → Bool,
      fval n w hn (Function.update x (enc n w s) false) ≠
        fval n w hn (Function.update x (enc n w s) true) := by
  refine ⟨fun idx => tab (dec n w idx), ?_⟩
  rw [ha_upd, ha_upd, fval_tab, fval_tab]
  exact h

lemma hc_loc_zero (n w : Nat) (hn : 0 < n) (i : Fin n) :
    loc n hn (i.val + (0 : Fin (w+1)).val) = i := by
  apply Fin.ext
  show (i.val + (0 : Fin (w+1)).val) % n = i.val
  rw [Fin.val_zero, Nat.add_zero, Nat.mod_eq_of_lt i.isLt]

lemma hc_upd (n w : Nat) (hn : 0 < n) (x0 x : Fin n → Bool) (i : Fin n) (b : Bool) :
    (∀ r : Fin n, Function.update
      (fun s : Fin n × (Fin (w+1) → Bool) =>
        decide (s.1 ≠ i ∧ s.2 = fun j : Fin (w+1) => x0 (loc n hn (s.1.val + j.val))))
      (i, fun j : Fin (w+1) => x0 (loc n hn (i.val + j.val))) b
      (r, fun j : Fin (w+1) => x (loc n hn (r.val + j.val))) = true) ↔ (x = x0 ∧ b = true) := by
  constructor
  · intro h
    have hpat : ∀ r : Fin n, (fun j : Fin (w+1) => x (loc n hn (r.val + j.val))) =
        fun j : Fin (w+1) => x0 (loc n hn (r.val + j.val)) := by
      intro r
      by_contra hne
      have hr := h r
      have hs : (r, fun j : Fin (w+1) => x (loc n hn (r.val + j.val))) ≠
          (i, fun j : Fin (w+1) => x0 (loc n hn (i.val + j.val))) := by
        intro he
        have h1 : r = i := congrArg Prod.fst he
        subst h1
        exact hne (congrArg Prod.snd he)
      rw [Function.update_of_ne hs] at hr
      simp only [decide_eq_true_eq] at hr
      exact hne hr.2
    have hx : x = x0 := by
      funext p
      have h0 := congrFun (hpat p) 0
      simp only [hc_loc_zero] at h0
      exact h0
    refine ⟨hx, ?_⟩
    subst hx
    have hi := h i
    rw [Function.update_self] at hi
    exact hi
  · rintro ⟨rfl, rfl⟩ r
    by_cases hr : r = i
    · subst hr
      rw [Function.update_self]
    · have hs : (r, fun j : Fin (w+1) => x (loc n hn (r.val + j.val))) ≠
          (i, fun j : Fin (w+1) => x (loc n hn (i.val + j.val))) := by
        intro he
        exact hr (congrArg Prod.fst he)
      rw [Function.update_of_ne hs]
      simp only [decide_eq_true_eq]
      exact ⟨hr, trivial⟩

lemma hc_dep_real (n w : Nat) (hn : 0 < n) (x0 : Fin n → Bool) (i : Fin n) :
    ∃ x : Fin (n*2^(w+1)) → Bool,
      fval n w hn (Function.update x
        (enc n w (i, fun j : Fin (w+1) => x0 (loc n hn (i.val + j.val)))) false) ≠
      fval n w hn (Function.update x
        (enc n w (i, fun j : Fin (w+1) => x0 (loc n hn (i.val + j.val)))) true) := by
  apply dep_mem n w hn (fun s : Fin n × (Fin (w+1) → Bool) =>
        decide (s.1 ≠ i ∧ s.2 = fun j : Fin (w+1) => x0 (loc n hn (s.1.val + j.val))))
  have h0 : cnt n w hn (Function.update (fun s : Fin n × (Fin (w+1) → Bool) =>
        decide (s.1 ≠ i ∧ s.2 = fun j : Fin (w+1) => x0 (loc n hn (s.1.val + j.val))))
      (i, fun j : Fin (w+1) => x0 (loc n hn (i.val + j.val))) false) = 0 := by
    unfold cnt
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    have := (hc_upd n w hn x0 x i false).1 hx
    exact Bool.false_ne_true this.2
  have h1 : cnt n w hn (Function.update (fun s : Fin n × (Fin (w+1) → Bool) =>
        decide (s.1 ≠ i ∧ s.2 = fun j : Fin (w+1) => x0 (loc n hn (s.1.val + j.val))))
      (i, fun j : Fin (w+1) => x0 (loc n hn (i.val + j.val))) true) = 1 := by
    unfold cnt
    rw [Finset.card_eq_one]
    refine ⟨x0, ?_⟩
    ext x
    rw [Finset.mem_filter, Finset.mem_singleton, hc_upd n w hn x0 x i true]
    simp
  rw [h0, h1]
  decide

def hc_xz (n m : Nat) (i : Fin n) (z : Fin m → Bool) : Fin n → Bool :=
  fun p => if h : (p.val + n - i.val) % n < m then z ⟨(p.val + n - i.val) % n, h⟩ else false

lemma hc_xz_at (n w : Nat) (hn : 0 < n) (m : Nat) (hmn : m ≤ n) (i : Fin n) (z : Fin m → Bool)
    (j : Nat) (hj : j < m) : hc_xz n m i z (loc n hn (i.val + j)) = z ⟨j, hj⟩ := by
  have hi := i.isLt
  have key : ((loc n hn (i.val + j)).val + n - i.val) % n = j := by
    show ((i.val + j) % n + n - i.val) % n = j
    by_cases hlt : i.val + j < n
    · rw [Nat.mod_eq_of_lt hlt]
      have : i.val + j + n - i.val = j + n := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · have h2 : (i.val + j) % n = i.val + j - n := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [h2]
      have : i.val + j - n + n - i.val = j := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
  unfold hc_xz
  have hlt : ((loc n hn (i.val + j)).val + n - i.val) % n < m := by rw [key]; exact hj
  rw [dif_pos hlt]
  congr 1
  exact Fin.ext key

lemma dep_count (n w : Nat) (hn : 0 < n) :
    n * 2^(min n (w+1)) ≤ ((Finset.univ : Finset (Fin (n*2^(w+1)))).filter (fun i =>
      ∃ x : Fin (n*2^(w+1)) → Bool,
        fval n w hn (Function.update x i false) ≠ fval n w hn (Function.update x i true))).card := by
  have hmn : min n (w+1) ≤ n := Nat.min_le_left _ _
  have hmw : min n (w+1) ≤ w+1 := Nat.min_le_right _ _
  have hcard : (Finset.univ : Finset (Fin n × (Fin (min n (w+1)) → Bool))).card =
      n * 2^(min n (w+1)) := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
  rw [← hcard]
  apply Finset.card_le_card_of_injOn (fun s : Fin n × (Fin (min n (w+1)) → Bool) =>
    enc n w (s.1, fun j : Fin (w+1) =>
      hc_xz n (min n (w+1)) s.1 s.2 (loc n hn (s.1.val + j.val))))
  · intro s _
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    exact hc_dep_real n w hn (hc_xz n (min n (w+1)) s.1 s.2) s.1
  · rintro ⟨i, z⟩ _ ⟨i', z'⟩ _ he
    have he2 := congrArg (dec n w) he
    simp only [dec_enc] at he2
    have h1 : i = i' := congrArg Prod.fst he2
    subst h1
    have h2 := congrArg Prod.snd he2
    simp only at h2
    have hz : z = z' := by
      funext j
      have h3 := congrFun h2 ⟨j.val, by omega⟩
      simp only at h3
      rw [hc_xz_at n w hn _ hmn i z j.val j.isLt, hc_xz_at n w hn _ hmn i z' j.val j.isLt] at h3
      exact h3
    rw [hz]

def Good (n w : Nat) (hn : 0 < n) (M : Nat) : Prop :=
  ∃ (slot : Fin M → Fin n × (Fin (w+1) → Bool)) (base : Fin n × (Fin (w+1) → Bool) → Bool),
    Function.Injective slot ∧ (∀ j, base (slot j) = false) ∧
    ∀ A : Finset (Fin M),
      cnt n w hn (fun s => base s || decide (s ∈ A.image slot)) % 2 = A.card % 2

lemma good_mono (n w : Nat) (hn : 0 < n) (M H : Nat) (h : Good n w hn M) (hle : H ≤ M) :
    Good n w hn H := by
  obtain ⟨slot, base, hinj, hbase, hpar⟩ := h
  refine ⟨fun j => slot (Fin.castLE hle j), base, ?_, fun j => hbase _, ?_⟩
  · intro a b hab
    exact Fin.castLE_injective hle (hinj hab)
  · intro A
    have h1 := hpar (A.image (Fin.castLE hle))
    rw [Finset.image_image, Finset.card_image_of_injective _ (Fin.castLE_injective hle)] at h1
    exact h1

def hc_xk (n m : Nat) (f : Fin m → Bool) : Fin n → Bool :=
  fun p => if h : p.val < m then f ⟨p.val, h⟩ else false

def hc_sl (n w : Nat) (hn : 0 < n) (m : Nat) (hm : 0 < m) (f : Fin m → Bool) :
    Fin n × (Fin (w+1) → Bool) :=
  (⟨0, hn⟩, fun j => f ⟨j.val % m, Nat.mod_lt _ hm⟩)

def hc_base (n w m : Nat) (s : Fin n × (Fin (w+1) → Bool)) : Bool :=
  decide (s.1.val ≠ 0 ∧ (m ≤ s.1.val → s.2 0 = false))

lemma hc_sl_inj (n w : Nat) (hn : 0 < n) (m : Nat) (hm : 0 < m) (hmw : m ≤ w+1)
    (f g : Fin m → Bool) (h : hc_sl n w hn m hm f = hc_sl n w hn m hm g) : f = g := by
  funext j
  have h2 := congrFun (congrArg Prod.snd h) ⟨j.val, by omega⟩
  simp only [hc_sl, Nat.mod_eq_of_lt j.isLt] at h2
  exact h2

lemma hc_xk_inj (n m : Nat) (hmn : m ≤ n) (f g : Fin m → Bool)
    (h : hc_xk n m f = hc_xk n m g) : f = g := by
  funext j
  have h2 := congrFun h ⟨j.val, by omega⟩
  simp only [hc_xk, dif_pos j.isLt] at h2
  exact h2

lemma hc_row0 (n w : Nat) (hn : 0 < n) (m : Nat) (hm : 0 < m)
    (hmod : ∀ j : Nat, j < w+1 → j % n = j % m) (f : Fin m → Bool) :
    ((⟨0, hn⟩ : Fin n), fun j : Fin (w+1) =>
      hc_xk n m f (loc n hn ((⟨0, hn⟩ : Fin n).val + j.val))) = hc_sl n w hn m hm f := by
  unfold hc_sl
  congr 1
  funext j
  have key : (loc n hn ((⟨0, hn⟩ : Fin n).val + j.val)).val = j.val % m := by
    show (0 + j.val) % n = j.val % m
    rw [Nat.zero_add]
    exact hmod j.val j.isLt
  unfold hc_xk
  have hlt : (loc n hn ((⟨0, hn⟩ : Fin n).val + j.val)).val < m := by
    rw [key]
    exact Nat.mod_lt _ hm
  rw [dif_pos hlt]
  congr 1
  exact Fin.ext key

lemma hc_pass (n w : Nat) (hn : 0 < n) (m : Nat) (hm : 0 < m) (hmn : m ≤ n) (hmw : m ≤ w+1)
    (hmod : ∀ j : Nat, j < w+1 → j % n = j % m) (ev : Fin (2^m) → (Fin m → Bool))
    (A : Finset (Fin (2^m))) (x : Fin n → Bool) :
    (∀ i : Fin n, (hc_base n w m (i, fun j : Fin (w+1) => x (loc n hn (i.val + j.val))) ||
      decide ((i, fun j : Fin (w+1) => x (loc n hn (i.val + j.val))) ∈
        A.image (fun k => hc_sl n w hn m hm (ev k)))) = true) ↔
    x ∈ A.image (fun k => hc_xk n m (ev k)) := by
  rw [Finset.mem_image]
  constructor
  · intro h
    have h0 := h ⟨0, hn⟩
    rw [Bool.or_eq_true, decide_eq_true_eq] at h0
    rcases h0 with h0 | h0
    · simp [hc_base] at h0
    · rw [Finset.mem_image] at h0
      obtain ⟨k, hk, hke⟩ := h0
      refine ⟨k, hk, ?_⟩
      funext p
      by_cases hp : p.val < m
      · have h2 := congrFun (congrArg Prod.snd hke) ⟨p.val, by omega⟩
        simp only [hc_sl, Nat.mod_eq_of_lt hp] at h2
        have hl : loc n hn (0 + p.val) = p := by
          apply Fin.ext
          show (0 + p.val) % n = p.val
          rw [Nat.zero_add, Nat.mod_eq_of_lt p.isLt]
        rw [hl] at h2
        unfold hc_xk
        rw [dif_pos hp]
        exact h2
      · have hpp := h p
        rw [Bool.or_eq_true, decide_eq_true_eq] at hpp
        have hx : x p = false := by
          rcases hpp with hpp | hpp
          · simp only [hc_base, decide_eq_true_eq] at hpp
            have h3 := hpp.2 (by omega)
            rw [hc_loc_zero] at h3
            exact h3
          · rw [Finset.mem_image] at hpp
            obtain ⟨k', _, hk'⟩ := hpp
            have h4 : (0 : Nat) = p.val := congrArg (fun s => s.1.val) hk'
            omega
        unfold hc_xk
        rw [dif_neg hp]
        exact hx.symm
  · rintro ⟨k, hk, rfl⟩ i
    rw [Bool.or_eq_true, decide_eq_true_eq]
    by_cases hi : i.val = 0
    · right
      have hi' : i = ⟨0, hn⟩ := Fin.ext hi
      rw [hi', hc_row0 n w hn m hm hmod (ev k)]
      exact Finset.mem_image_of_mem _ hk
    · left
      simp only [hc_base, decide_eq_true_eq]
      refine ⟨hi, ?_⟩
      intro hmi
      rw [hc_loc_zero]
      unfold hc_xk
      rw [dif_neg (by omega)]

lemma hc_good (n w : Nat) (hn : 0 < n) (m : Nat) (hm : 0 < m) (hmn : m ≤ n) (hmw : m ≤ w+1)
    (hmod : ∀ j : Nat, j < w+1 → j % n = j % m) : Good n w hn (2^m) := by
  have hc : Fintype.card (Fin m → Bool) = 2^m := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  obtain ⟨ev⟩ : Nonempty (Fin (2^m) ≃ (Fin m → Bool)) := ⟨(Fintype.equivFinOfCardEq hc).symm⟩
  refine ⟨fun k => hc_sl n w hn m hm (ev k), hc_base n w m, ?_, ?_, ?_⟩
  · intro a b hab
    exact ev.injective (hc_sl_inj n w hn m hm hmw _ _ hab)
  · intro j
    simp [hc_base, hc_sl]
  · intro A
    have hcnt : cnt n w hn (fun s => hc_base n w m s ||
        decide (s ∈ A.image (fun k => hc_sl n w hn m hm (ev k)))) = A.card := by
      unfold cnt
      have hf : ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => ∀ i : Fin n,
          (hc_base n w m (i, fun j : Fin (w+1) => x (loc n hn (i.val + j.val))) ||
          decide ((i, fun j : Fin (w+1) => x (loc n hn (i.val + j.val))) ∈
            A.image (fun k => hc_sl n w hn m hm (ev k)))) = true)) =
          A.image (fun k => hc_xk n m (ev k)) := by
        ext x
        rw [Finset.mem_filter, hc_pass n w hn m hm hmn hmw hmod ev A x]
        simp only [Finset.mem_univ, true_and]
      rw [hf]
      apply Finset.card_image_of_injective
      intro a b hab
      exact ev.injective (hc_xk_inj n m hmn _ _ hab)
    rw [hcnt]

lemma good_direct (n w : Nat) (hn : 0 < n) : Good n w hn (2^(min n (w+1))) := by
  apply hc_good n w hn (min n (w+1)) (by omega) (Nat.min_le_left _ _) (Nat.min_le_right _ _)
  intro j hj
  rcases Nat.le_total n (w+1) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hj]

lemma hb_plug (n w H : Nat) (slot : Fin H → Fin n × (Fin (w+1) → Bool))
    (base : Fin n × (Fin (w+1) → Bool) → Bool) (hbase : ∀ j, base (slot j) = false)
    (y : Fin H → Bool) (idx : Fin (n*2^(w+1))) :
    (if idx ∈ Finset.univ.image (fun j => enc n w (slot j)) then
      decide (∃ j, (fun j => enc n w (slot j)) j = idx ∧ y j = true)
      else (fun idx => base (dec n w idx)) idx) =
    (base (dec n w idx) ||
      decide (dec n w idx ∈ (Finset.univ.filter (fun j => y j = true)).image slot)) := by
  by_cases hm : ∃ j, enc n w (slot j) = idx
  · obtain ⟨j0, rfl⟩ := hm
    rw [if_pos (Finset.mem_image.mpr ⟨j0, Finset.mem_univ _, rfl⟩), dec_enc, hbase, Bool.false_or]
    apply decide_eq_decide.mpr
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, hy⟩
      have h2 := congrArg (dec n w) hj
      rw [dec_enc, dec_enc] at h2
      exact ⟨j, hy, h2⟩
    · rintro ⟨j, hy, hj⟩
      exact ⟨j, by rw [hj], hy⟩
  · have h1 : idx ∉ Finset.univ.image (fun j => enc n w (slot j)) := by
      intro hc
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hc
      exact hm ⟨j, hj⟩
    have h2 : dec n w idx ∉ (Finset.univ.filter (fun j => y j = true)).image slot := by
      intro hc
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hc
      exact hm ⟨j, by rw [hj, enc_dec]⟩
    rw [if_neg h1, decide_eq_false h2, Bool.or_false]

lemma hb_evalplug (n w : Nat) (hn : 0 < n) (H : Nat)
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hev : ∀ raw : Fin (n*2^(w+1)) → Bool, C.eval (List.ofFn raw) = fval n w hn raw)
    (slot : Fin H → Fin n × (Fin (w+1) → Bool))
    (base : Fin n × (Fin (w+1) → Bool) → Bool) (hbase : ∀ j, base (slot j) = false)
    (hpar : ∀ A : Finset (Fin H),
      cnt n w hn (fun s => base s || decide (s ∈ A.image slot)) % 2 = A.card % 2)
    (y : Fin H → Bool) :
    C.eval (List.ofFn (fun idx : Fin (n*2^(w+1)) =>
      if idx ∈ Finset.univ.image (fun j => enc n w (slot j)) then
      decide (∃ j, (fun j => enc n w (slot j)) j = idx ∧ y j = true)
      else (fun idx => base (dec n w idx)) idx)) =
    ((Finset.univ.filter (fun j => y j = true)).card).testBit 0 := by
  have h1 : (fun idx : Fin (n*2^(w+1)) =>
      if idx ∈ Finset.univ.image (fun j => enc n w (slot j)) then
      decide (∃ j, (fun j => enc n w (slot j)) j = idx ∧ y j = true)
      else (fun idx => base (dec n w idx)) idx) =
      fun idx => (fun s => base s ||
        decide (s ∈ (Finset.univ.filter (fun j => y j = true)).image slot)) (dec n w idx) :=
    funext (hb_plug n w H slot base hbase y)
  rw [h1, hev]
  refine (fval_tab n w hn (fun s => base s ||
        decide (s ∈ (Finset.univ.filter (fun j => y j = true)).image slot))).trans ?_
  rw [Nat.testBit_zero, Nat.testBit_zero, hpar]

lemma hb_slotdep (n w : Nat) (hn : 0 < n) (H : Nat)
    (slot : Fin H → Fin n × (Fin (w+1) → Bool))
    (base : Fin n × (Fin (w+1) → Bool) → Bool) (hbase : ∀ j, base (slot j) = false)
    (hpar : ∀ A : Finset (Fin H),
      cnt n w hn (fun s => base s || decide (s ∈ A.image slot)) % 2 = A.card % 2)
    (j : Fin H) :
    (cnt n w hn (Function.update base (slot j) false)).testBit 0 ≠
      (cnt n w hn (Function.update base (slot j) true)).testBit 0 := by
  have e0 : Function.update base (slot j) false =
      fun s => base s || decide (s ∈ (∅ : Finset (Fin H)).image slot) := by
    funext s
    by_cases hs : s = slot j
    · subst hs
      simp [hbase]
    · simp [Function.update_of_ne hs]
  have e1 : Function.update base (slot j) true =
      fun s => base s || decide (s ∈ ({j} : Finset (Fin H)).image slot) := by
    funext s
    by_cases hs : s = slot j
    · subst hs
      simp
    · simp [hs]
  have p0 := hpar ∅
  have p1 := hpar {j}
  rw [← e0] at p0
  rw [← e1] at p1
  rw [Nat.testBit_zero, Nat.testBit_zero, p0, p1]
  simp

lemma hb_parity (H : Nat) (hH : 0 < H) (D : PEqualNP.CircuitLowerBounds.Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo D)
    (hev : ∀ y : Fin H → Bool, D.eval (List.ofFn y) =
      ((Finset.univ.filter (fun j => y j = true)).card).testBit 0) :
    3*(H-1) ≤ D.gates.length - (D.gates.filter (fun g =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length ∧
    4*(H-1) ≤ D.gates.length := by
  have hm := PEqualNP.Outside.L_clb_127.T25689 H H hH
  dsimp only at hm
  have hm2 := (hm (fun i => i) (fun j x => x j) (fun j => ⟨j, rfl⟩)
    (fun j x y hxy => hxy j rfl)
    (fun i => ⟨fun _ => false, by simp, by simp⟩)
    (fun j => ⟨⟨[], j.val⟩, by intro g hg; simp at hg, by
      simp [PEqualNP.CircuitLowerBounds.Circuit.size, Finset.filter_eq'], by
      intro x
      simp [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]⟩)).2
    D ⟨hfan, hev⟩
  simp only [PEqualNP.CircuitLowerBounds.Circuit.size] at hm2
  omega

lemma lower_core (n w : Nat) (hn : 0 < n) (H : Nat) (hH : 0 < H) (hg : Good n w hn H)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hev : ∀ raw : Fin (n*2^(w+1)) → Bool, C.eval (List.ofFn raw) = fval n w hn raw) :
    (n*2^(min n (w+1)) - H) + 3*(H-1) ≤ C.size - (C.gates.filter (fun g =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length ∧
    (n*2^(min n (w+1)) - H) + 4*(H-1) ≤ C.size := by
  obtain ⟨slot, base, hinj, hbase, hpar⟩ := hg
  have winj : Function.Injective (fun j => enc n w (slot j)) := by
    intro a b hab
    have h2 := congrArg (dec n w) hab
    rw [dec_enc, dec_enc] at h2
    exact hinj h2
  have hpl := hb_evalplug n w hn H C hev slot base hbase hpar
  have h586 := PEqualNP.Outside.L_clb_127.T586 (n*2^(w+1)) H C hfan
    (fun j => enc n w (slot j)) (fun idx => base (dec n w idx)) winj
  have hnc : ((Finset.univ.filter (fun j : Fin H => (fun _ => false : Fin H → Bool) j = true)).card).testBit 0
      ≠ ((Finset.univ.filter (fun j : Fin H =>
        (fun j => decide (j = (⟨0, hH⟩ : Fin H))) j = true)).card).testBit 0 := by
    simp [Finset.filter_eq']
  obtain ⟨D, hDfan, hDbin, hDinv, hDev⟩ := h586 ⟨fun _ => false,
    fun j => decide (j = (⟨0, hH⟩ : Fin H)), fun heq =>
      hnc ((hpl _).symm.trans (heq.trans (hpl _)))⟩
  have hDev2 : ∀ y : Fin H → Bool, D.eval (List.ofFn y) =
      ((Finset.univ.filter (fun j => y j = true)).card).testBit 0 :=
    fun y => (hDev y).trans (hpl y)
  have hD := hb_parity H hH D hDfan hDev2
  have hE : n*2^(min n (w+1)) ≤ ((Finset.univ : Finset (Fin (n*2^(w+1)))).filter (fun i =>
      ∃ x : Fin (n*2^(w+1)) → Bool, C.eval (List.ofFn (Function.update x i false)) ≠
        C.eval (List.ofFn (Function.update x i true)))).card := by
    simp only [hev]
    exact dep_count n w hn
  have hHe : H ≤ ((Finset.univ : Finset (Fin (n*2^(w+1)))).filter (fun i =>
      ∃ x : Fin (n*2^(w+1)) → Bool, C.eval (List.ofFn (Function.update x i false)) ≠
        C.eval (List.ofFn (Function.update x i true)))).card := by
    have h3 := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin H)))
      (t := ((Finset.univ : Finset (Fin (n*2^(w+1)))).filter (fun i =>
      ∃ x : Fin (n*2^(w+1)) → Bool, C.eval (List.ofFn (Function.update x i false)) ≠
        C.eval (List.ofFn (Function.update x i true))))) (fun j => enc n w (slot j))
      (by
        intro j _
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simp only [hev]
        exact dep_mem n w hn base (slot j) (hb_slotdep n w hn H slot base hbase hpar j))
      (fun a _ b _ hab => winj hab)
    rwa [Finset.card_univ, Fintype.card_fin] at h3
  have hDbin2 : (D.gates.length - (D.gates.filter (fun g =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length) +
      ((Finset.univ : Finset (Fin (n*2^(w+1)))).filter (fun i =>
      ∃ x : Fin (n*2^(w+1)) → Bool, C.eval (List.ofFn (Function.update x i false)) ≠
        C.eval (List.ofFn (Function.update x i true)))).card ≤
      (C.gates.length - (C.gates.filter (fun g =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length) + H :=
    hDbin
  have hDinv2 : (D.gates.filter (fun g =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length ≤
      (C.gates.filter (fun g =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length :=
    hDinv
  have hiC := List.length_filter_le (fun g : PEqualNP.CircuitLowerBounds.Gate =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _)) C.gates
  have hiD := List.length_filter_le (fun g : PEqualNP.CircuitLowerBounds.Gate =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _)) D.gates
  simp only [PEqualNP.CircuitLowerBounds.Circuit.size]
  generalize ((Finset.univ : Finset (Fin (n*2^(w+1)))).filter (fun i =>
      ∃ x : Fin (n*2^(w+1)) → Bool, C.eval (List.ofFn (Function.update x i false)) ≠
        C.eval (List.ofFn (Function.update x i true)))).card = e at hE hHe hDbin2
  generalize n*2^(min n (w+1)) = E at hE ⊢
  generalize (C.gates.filter (fun g =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length = iC
    at hDbin2 hDinv2 hiC ⊢
  generalize (D.gates.filter (fun g =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length = iD
    at hDbin2 hDinv2 hiD hD
  omega


end PEqualNP.Outside.L_clb_127.C120

theorem PEqualNP.Outside.L_clb_127 : ¬ (let n := 3
let w := 1
let P := 2^(w+1)
let inv := fun (G : PEqualNP.CircuitLowerBounds.Circuit) =>
  (G.gates.filter (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length
let binary := fun (G : PEqualNP.CircuitLowerBounds.Circuit) => G.size - inv G
let loc := fun k : Nat => (⟨k % n, Nat.mod_lt _ (Nat.succ_pos 2)⟩ : Fin n)
let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.FanInTwo C ∧ ∀ raw : Fin (n*P) → Bool,
    let entries := List.ofFn raw
    let pass := fun (x : Fin n → Bool) => ∀ i : Fin n,
      let word := ∑ j : Fin (w+1), if x (loc (i.val+j.val)) then 2^j.val else 0
      entries.getD (i.val*P+word) false = true
    C.eval entries = (((Finset.univ : Finset (Fin n → Bool)).filter pass).card).testBit 0
∃ C, fits C ∧ binary C ≤ 16) := by
  intro h
  obtain ⟨C, hfit, hle⟩ := h
  have key := (PEqualNP.Outside.L_clb_127.C120.lower_core 3 1 (by decide) 4 (by decide)
    (PEqualNP.Outside.L_clb_127.C120.good_mono 3 1 (by decide) _ 4
      (PEqualNP.Outside.L_clb_127.C120.good_direct 3 1 (by decide)) (by decide)) C hfit.1 hfit.2).1
  have e : (3 * 2 ^ (min 3 (1+1)) - 4) + 3 * (4-1) = 17 := by decide
  rw [e] at key
  exact absurd (le_trans key hle) (by decide)
