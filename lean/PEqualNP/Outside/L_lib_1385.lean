import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1385
open PEqualNP.CircuitLowerBounds

def wr (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem wr_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wr (gs ++ [g]) x = wr gs x ++ [g.op.eval (g.inputs.map fun i => (wr gs x).getD i false)] := by
  simp [wr, List.foldl_append]

theorem wr_len (gs : List Gate) (x : List Bool) : (wr gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wr]
  | append_singleton gs g ih =>
    rw [wr_snoc, List.length_append, ih, List.length_append, List.length_singleton,
      List.length_singleton, Nat.add_assoc]

theorem wr_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (wr gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [wr_snoc, List.getD_append _ _ _ _ (by rw [wr_len]; omega)]; exact ih

def Has (gs : List Gate) (x : List Bool) (i : ℕ) (v : Bool) : Prop :=
  i < x.length + gs.length ∧ (wr gs x).getD i false = v

theorem Has.old {gs : List Gate} {x : List Bool} {i : ℕ} {v : Bool} (g : Gate) (h : Has gs x i v) :
    Has (gs ++ [g]) x i v := by
  refine ⟨by rw [List.length_append, List.length_singleton]; have := h.1; omega, ?_⟩
  rw [wr_snoc, List.getD_append _ _ _ _ (by rw [wr_len]; exact h.1)]
  exact h.2

theorem Has.new (gs : List Gate) (x : List Bool) (g : Gate) (k : ℕ) (hk : k = x.length + gs.length) :
    Has (gs ++ [g]) x k (g.op.eval (g.inputs.map fun i => (wr gs x).getD i false)) := by
  subst hk
  refine ⟨by rw [List.length_append, List.length_singleton]; omega, ?_⟩
  rw [wr_snoc, List.getD_append_right _ _ _ _ (le_of_eq (wr_len gs x)), wr_len, Nat.sub_self]
  rfl

def gN (i : ℕ) : Gate := ⟨GateOp.not, [i]⟩
def gA (i j : ℕ) : Gate := ⟨GateOp.and, [i, j]⟩
def gO (i j : ℕ) : Gate := ⟨GateOp.or, [i, j]⟩

theorem Has.not {gs : List Gate} {x : List Bool} {i : ℕ} {v : Bool} (k : ℕ)
    (hk : k = x.length + gs.length) (h : Has gs x i v) : Has (gs ++ [gN i]) x k (!v) := by
  obtain ⟨_, rfl⟩ := h
  have e := Has.new gs x (gN i) k hk
  refine ⟨e.1, e.2.trans ?_⟩
  simp [gN, GateOp.eval]

theorem Has.and {gs : List Gate} {x : List Bool} {i j : ℕ} {u v : Bool} (k : ℕ)
    (hk : k = x.length + gs.length) (h1 : Has gs x i u) (h2 : Has gs x j v) :
    Has (gs ++ [gA i j]) x k (u && v) := by
  obtain ⟨_, rfl⟩ := h1
  obtain ⟨_, rfl⟩ := h2
  have e := Has.new gs x (gA i j) k hk
  refine ⟨e.1, e.2.trans ?_⟩
  simp [gA, GateOp.eval]

theorem Has.or {gs : List Gate} {x : List Bool} {i j : ℕ} {u v : Bool} (k : ℕ)
    (hk : k = x.length + gs.length) (h1 : Has gs x i u) (h2 : Has gs x j v) :
    Has (gs ++ [gO i j]) x k (u || v) := by
  obtain ⟨_, rfl⟩ := h1
  obtain ⟨_, rfl⟩ := h2
  have e := Has.new gs x (gO i j) k hk
  refine ⟨e.1, e.2.trans ?_⟩
  simp [gO, GateOp.eval]

def rb (m : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < m + j

theorem rb_snoc {m : ℕ} {gs : List Gate} (g : Gate) (h : rb m gs)
    (hg : ∀ i ∈ g.inputs, i < m + gs.length) : rb m (gs ++ [g]) := by
  intro j hj i hi
  rw [List.length_append, List.length_singleton] at hj
  by_cases hjl : j < gs.length
  · rw [List.getD_append _ _ _ _ hjl] at hi
    exact h j hjl i hi
  · have : j = gs.length := by omega
    subst this
    rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self] at hi
    exact hg i hi

theorem rb_of_snoc {m : ℕ} {gs : List Gate} {g : Gate} (h : rb m (gs ++ [g])) :
    rb m gs ∧ ∀ i ∈ g.inputs, i < m + gs.length := by
  constructor
  · intro j hj i hi
    refine h j (by rw [List.length_append, List.length_singleton]; omega) i ?_
    rw [List.getD_append _ _ _ _ hj]; exact hi
  · intro i hi
    refine h gs.length (by rw [List.length_append, List.length_singleton]; omega) i ?_
    rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]; exact hi

def rl (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

theorem rb_map (ρ : ℕ → ℕ) (m m' : ℕ) (hb : ∀ k i, i < m + k → ρ i < m' + k) (gs : List Gate)
    (h : rb m gs) : rb m' (gs.map (rl ρ)) := by
  intro j hj i hi
  rw [List.length_map] at hj
  have e1 : (gs.map (rl ρ)).getD j ⟨GateOp.or, []⟩ = rl ρ (gs[j]) := by
    simp [List.getD_eq_getElem?_getD, hj]
  have e2 : gs.getD j ⟨GateOp.or, []⟩ = gs[j] := by
    simp [List.getD_eq_getElem?_getD, hj]
  rw [e1] at hi
  obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
  exact hb _ _ (h j hj i' (e2 ▸ hi'))

theorem rl_wires (ρ : ℕ → ℕ) (m m' : ℕ) (x x' : List Bool) (hm : x.length = m)
    (hm' : x'.length = m') (hρ : ∀ k, ρ (m + k) = m' + k) (hlt : ∀ i < m, ρ i < m')
    (hx : ∀ i < m, x'.getD (ρ i) false = x.getD i false) :
    ∀ gs : List Gate, rb m gs → ∀ i < m + gs.length,
      (wr (gs.map (rl ρ)) x').getD (ρ i) false = (wr gs x).getD i false := by
  have hb : ∀ (k i : ℕ), i < m + k → ρ i < m' + k := by
    intro k i hi
    by_cases h : i < m
    · have := hlt i h; omega
    · have := hρ (i - m); rw [show m + (i - m) = i by omega] at this; omega
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ i hi
    have hi' : i < m := by simpa using hi
    show (wr [] x').getD (ρ i) false = (wr [] x).getD i false
    exact hx i hi'
  | append_singleton gs g ih =>
    intro hr i hi
    obtain ⟨hr1, hr2⟩ := rb_of_snoc hr
    have ih' := ih hr1
    rw [List.length_append, List.length_singleton] at hi
    rw [List.map_append, List.map_singleton, wr_snoc, wr_snoc]
    have hv : (rl ρ g).op.eval ((rl ρ g).inputs.map fun i => (wr (gs.map (rl ρ)) x').getD i false)
        = g.op.eval (g.inputs.map fun i => (wr gs x).getD i false) := by
      show g.op.eval ((g.inputs.map ρ).map fun i => (wr (gs.map (rl ρ)) x').getD i false) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact ih' i (hr2 i hi)
    rw [hv]
    by_cases h : i < m + gs.length
    · rw [List.getD_append _ _ _ _ (by rw [wr_len, List.length_map, hm']; exact hb _ _ h),
        List.getD_append _ _ _ _ (by rw [wr_len, hm]; exact h)]
      exact ih' i h
    · have : i = m + gs.length := by omega
      subst this
      rw [hρ, List.getD_append_right _ _ _ _ (le_of_eq (by rw [wr_len, List.length_map, hm'])),
        List.getD_append_right _ _ _ _ (le_of_eq (by rw [wr_len, hm]))]
      rw [wr_len, wr_len, List.length_map, hm, hm', Nat.sub_self, Nat.sub_self]

theorem xval (n l i : ℕ) :
    (List.ofFn (fun j : Fin n => decide (j.val < l)) ++ [false, true]).getD i false
      = (decide (i < n ∧ i < l) || decide (i = n + 1)) := by
  by_cases hi : i < n
  · rw [List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact hi)]
    have : i ≠ n + 1 := by omega
    simp [List.getD_eq_getElem?_getD, hi, this]
  · have : i = n ∨ i = n + 1 ∨ n + 2 ≤ i := by omega
    rw [List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]; omega), List.length_ofFn]
    rcases this with rfl | rfl | h
    · simp
    · simp
    · have h2 : ¬ (i = n + 1) := by omega
      obtain ⟨k, hk⟩ : ∃ k, i - n = k + 2 := ⟨i - n - 2, by omega⟩
      rw [hk]
      simp [hi, h2]

def tail (gs : List Gate) (B u v p q r : ℕ) : List Gate :=
  gs ++ [gN p] ++ [gA u B] ++ [gN q] ++ [gA v (B + 2)] ++ [gN u] ++ [gO r p]
    ++ [gO (B + 4) (B + 3)] ++ [gA (B + 5) (B + 6)]

theorem len1 (gs : List Gate) (g : Gate) : (gs ++ [g]).length = gs.length + 1 := by
  rw [List.length_append, List.length_singleton]

theorem tail_len (gs : List Gate) (B u v p q r : ℕ) :
    (tail gs B u v p q r).length = gs.length + 8 := by
  simp only [tail, len1]

theorem tail_has (gs : List Gate) (x : List Bool) (B u v p q r : ℕ) (bu bv bp bq br : Bool)
    (hB : B = x.length + gs.length)
    (hu : Has gs x u bu) (hv : Has gs x v bv) (hp : Has gs x p bp) (hq : Has gs x q bq)
    (hr : Has gs x r br) :
    Has (tail gs B u v p q r) x (B + 1) (bu && !bp) ∧
    Has (tail gs B u v p q r) x (B + 3) (bv && !bq) ∧
    Has (tail gs B u v p q r) x (B + 7) ((br || bp) && (!bu || (bv && !bq))) ∧
    ∀ i w, Has gs x i w → Has (tail gs B u v p q r) x i w := by
  have l1 : ∀ {i w}, Has gs x i w → Has (gs ++ [gN p]) x i w := fun h => h.old _
  have l2 : ∀ {i w}, Has gs x i w → Has (gs ++ [gN p] ++ [gA u B]) x i w := fun h => (l1 h).old _
  have l3 : ∀ {i w}, Has gs x i w → Has (gs ++ [gN p] ++ [gA u B] ++ [gN q]) x i w :=
    fun h => (l2 h).old _
  have l4 : ∀ {i w}, Has gs x i w →
      Has (gs ++ [gN p] ++ [gA u B] ++ [gN q] ++ [gA v (B + 2)]) x i w := fun h => (l3 h).old _
  have l5 : ∀ {i w}, Has gs x i w →
      Has (gs ++ [gN p] ++ [gA u B] ++ [gN q] ++ [gA v (B + 2)] ++ [gN u]) x i w :=
    fun h => (l4 h).old _
  have n0 := Has.not B (by omega) hp
  have a1 := Has.and (B + 1) (by simp only [len1]; omega) (l1 hu) n0
  have n2 := Has.not (B + 2) (by simp only [len1]; omega) (l2 hq)
  have a3 := Has.and (B + 3) (by simp only [len1]; omega) (l3 hv) n2
  have n4 := Has.not (B + 4) (by simp only [len1]; omega) (l4 hu)
  have o5 := Has.or (B + 5) (by simp only [len1]; omega) (l5 hr) (l5 hp)
  have o6 := Has.or (B + 6) (by simp only [len1]; omega) ((n4.old (gO r p)))
    ((a3.old (gN u)).old (gO r p))
  have a7 := Has.and (B + 7) (by simp only [len1]; omega) (o5.old (gO (B + 4) (B + 3))) o6
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (((((a1.old _).old _).old _).old _).old _).old _
  · exact (((a3.old _).old _).old _).old _
  · exact a7
  · intro i w h
    exact (((l5 h).old _).old _).old _

def F2 (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem F2_snoc {gs : List Gate} (g : Gate) (h : F2 gs)
    (h1 : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (h2 : g.inputs.length ≤ 2) :
    F2 (gs ++ [g]) := by
  intro g' hg'
  rcases List.mem_append.mp hg' with h' | h'
  · exact h g' h'
  · rw [List.mem_singleton] at h'; subst h'; exact ⟨h1, h2⟩

theorem F2_N {gs : List Gate} (i : ℕ) (h : F2 gs) : F2 (gs ++ [gN i]) :=
  F2_snoc _ h (by simp [gN]) (by simp [gN])
theorem F2_A {gs : List Gate} (i j : ℕ) (h : F2 gs) : F2 (gs ++ [gA i j]) :=
  F2_snoc _ h (by simp [gA]) (by simp [gA])
theorem F2_O {gs : List Gate} (i j : ℕ) (h : F2 gs) : F2 (gs ++ [gO i j]) :=
  F2_snoc _ h (by simp [gO]) (by simp [gO])

theorem F2_tail (gs : List Gate) (B u v p q r : ℕ) (h : F2 gs) : F2 (tail gs B u v p q r) :=
  F2_A _ _ (F2_O _ _ (F2_O _ _ (F2_N _ (F2_A _ _ (F2_N _ (F2_A _ _ (F2_N _ h)))))))

theorem rb_tail (m : ℕ) (gs : List Gate) (B u v p q r : ℕ) (hB : B = m + gs.length)
    (hu : u < B) (hv : v < B) (hp : p < B) (hq : q < B) (hr : r < B) (h : rb m gs) :
    rb m (tail gs B u v p q r) := by
  refine rb_snoc _ (rb_snoc _ (rb_snoc _ (rb_snoc _ (rb_snoc _ (rb_snoc _ (rb_snoc _
    (rb_snoc _ h ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  all_goals
    intro i hi
    simp only [gN, gA, gO, List.mem_cons, List.not_mem_nil, or_false] at hi
    try simp only [len1]
    omega

def nc (gs : List Gate) : ℕ := PEqualNP.NotBracket.notCount ⟨gs, 0⟩

theorem nc_snoc_N (gs : List Gate) (i : ℕ) : nc (gs ++ [gN i]) = nc gs + 1 := by
  simp [nc, PEqualNP.NotBracket.notCount, gN, List.filter_append]
theorem nc_snoc_A (gs : List Gate) (i j : ℕ) : nc (gs ++ [gA i j]) = nc gs := by
  simp [nc, PEqualNP.NotBracket.notCount, gA, List.filter_append]
theorem nc_snoc_O (gs : List Gate) (i j : ℕ) : nc (gs ++ [gO i j]) = nc gs := by
  simp [nc, PEqualNP.NotBracket.notCount, gO, List.filter_append]

theorem nc_tail (gs : List Gate) (B u v p q r : ℕ) : nc (tail gs B u v p q r) = nc gs + 3 := by
  simp only [tail, nc_snoc_N, nc_snoc_A, nc_snoc_O]

theorem nc_map (ρ : ℕ → ℕ) (gs : List Gate) : nc (gs.map (rl ρ)) = nc gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [nc, PEqualNP.NotBracket.notCount, List.map_cons, List.filter_cons] at ih ⊢
    have : (rl ρ g).op = g.op := rfl
    rw [this]
    split_ifs
    · simp only [List.length_cons, ih]
    · exact ih

def Fit (n a p b s : ℕ) (W : ℕ → Fin a → Bool) : Prop :=
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ (∀ i, tap i < n+2+C.size) ∧
    C.size - PEqualNP.NotBracket.notCount C ≤ p ∧ PEqualNP.NotBracket.notCount C ≤ b ∧ C.size ≤ s ∧
    ∀ (l : Fin (n+1)) i, (C.wires
      (List.ofFn (fun j : Fin n => decide (j.val < l.val)) ++ [false,true])).getD (tap i) false = W l.val i

def rho (h n i : ℕ) : ℕ := if i < h then i else if i < n then i + 2 else i + 4
def ret (h n l : ℕ) : ℕ := if l ≤ h then l else min n (max h (l-2))

theorem part1 (n a p b s h : ℕ) (W : ℕ → Fin (a+1) → Bool) (hh : h < n) (hWn : W n 0 = false)
    (hf : Fit n (a+1) p b s W) :
    Fit (n+4) (a+4) (p+5) (b+3) (s+8) (fun (l : Nat) (i : Fin (a+4)) =>
      if i.val < a+1 then W (ret h n l) (Fin.ofNat (a+1) i.val)
      else if i.val = a+1 then decide (h+1 ≤ l ∧ l < n+3)
      else if i.val = a+2 then decide (h+2 ≤ l ∧ l < n+4)
      else if l = h+1 then false else if l = n+3 then true else W (ret h n l) 0) := by
  obtain ⟨C, tap, hF, hR, -, htap, hp, hb, hs, hval⟩ := hf
  have hbd : ∀ k i, i < n + 2 + k → rho h n i < n + 4 + 2 + k := by
    intro k i hi; unfold rho; split_ifs <;> omega
  have hlen0 : (C.gates.map (rl (rho h n))).length = C.size := by
    rw [List.length_map]; rfl
  have hB : n + 6 + C.size = n + 4 + 2 + (C.gates.map (rl (rho h n))).length := by
    rw [hlen0]
  have hF0 : F2 (C.gates.map (rl (rho h n))) := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    have := hF g' hg'
    exact ⟨this.1, by simp only [rl, List.length_map]; exact this.2⟩
  have hR0 : rb (n + 4 + 2) (C.gates.map (rl (rho h n))) := rb_map _ (n + 2) _ hbd _ hR
  have ht0 := htap 0
  have hr0 := hbd _ _ ht0
  have hnc : PEqualNP.NotBracket.notCount C = nc C.gates := rfl
  refine ⟨⟨tail (C.gates.map (rl (rho h n))) (n + 6 + C.size) h (h+1) (n+2) (n+3) (rho h n (tap 0)), 0⟩,
    fun i => if i.val < a+1 then rho h n (tap (Fin.ofNat (a+1) i.val))
      else if i.val = a+1 then n + 6 + C.size + 1 else if i.val = a+2 then n + 6 + C.size + 3
      else n + 6 + C.size + 7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact F2_tail _ _ _ _ _ _ _ hF0
  · exact rb_tail _ _ _ _ _ _ _ _ hB (by omega) (by omega) (by omega) (by omega) (by omega) hR0
  · exact Nat.lt_of_lt_of_le (by omega : 0 < n + 4 + 2) (Nat.le_add_right _ _)
  · intro i
    show (if i.val < a+1 then rho h n (tap (Fin.ofNat (a+1) i.val))
      else if i.val = a+1 then n + 6 + C.size + 1 else if i.val = a+2 then n + 6 + C.size + 3
      else n + 6 + C.size + 7) < n + 4 + 2 + (tail _ _ _ _ _ _ _).length
    rw [tail_len, hlen0]
    split_ifs
    · have := hbd _ _ (htap (Fin.ofNat (a+1) i.val)); omega
    · omega
    · omega
    · omega
  · show (tail _ _ _ _ _ _ _).length - nc (tail _ _ _ _ _ _ _) ≤ p + 5
    rw [tail_len, nc_tail, nc_map, hlen0]
    rw [hnc] at hp; omega
  · show nc (tail _ _ _ _ _ _ _) ≤ b + 3
    rw [nc_tail, nc_map]
    rw [hnc] at hb; omega
  · show (tail _ _ _ _ _ _ _).length ≤ s + 8
    rw [tail_len, hlen0]; omega
  · intro l i
    have hl := l.isLt
    have hretle : ret h n l.val ≤ n := by unfold ret; split_ifs <;> omega
    have hxlen : (List.ofFn (fun j : Fin (n+4) => decide (j.val < l.val)) ++ [false, true]).length
        = n + 4 + 2 := by simp
    have hxx : ∀ i < n + 2,
        (List.ofFn (fun j : Fin (n+4) => decide (j.val < l.val)) ++ [false, true]).getD (rho h n i) false
        = (List.ofFn (fun j : Fin n => decide (j.val < ret h n l.val)) ++ [false, true]).getD i false := by
      intro i hi
      rw [xval, xval]
      have e1 : (rho h n i < n + 4 ∧ rho h n i < l.val) ↔ (i < n ∧ i < ret h n l.val) := by
        unfold rho ret; split_ifs <;> omega
      have e2 : (rho h n i = n + 4 + 1) ↔ (i = n + 1) := by
        unfold rho; split_ifs <;> omega
      rw [decide_eq_decide.mpr e1, decide_eq_decide.mpr e2]
    have key := rl_wires (rho h n) (n + 2) (n + 4 + 2) _ _ (by simp) hxlen
      (by intro k; unfold rho; split_ifs <;> omega) (fun i hi => by have := hbd 0 i hi; omega)
      hxx C.gates hR
    have hv := hval ⟨ret h n l.val, by omega⟩
    have hT : ∀ i, Has (C.gates.map (rl (rho h n)))
        (List.ofFn (fun j : Fin (n+4) => decide (j.val < l.val)) ++ [false, true])
        (rho h n (tap i)) (W (ret h n l.val) i) := fun i =>
      ⟨by rw [hxlen]; exact hbd _ _ (by rw [hlen0]; exact htap i), (key _ (htap i)).trans (hv i)⟩
    have hin : ∀ k, k < n + 4 → Has (C.gates.map (rl (rho h n)))
        (List.ofFn (fun j : Fin (n+4) => decide (j.val < l.val)) ++ [false, true])
        k (decide (k < l.val)) := by
      intro k hk
      refine ⟨by rw [hxlen]; omega, ?_⟩
      rw [wr_input _ _ _ (by rw [hxlen]; omega), xval]
      have e1 : (k < n + 4 ∧ k < l.val) ↔ k < l.val := by omega
      have e2 : ¬ (k = n + 4 + 1) := by omega
      rw [decide_eq_decide.mpr e1, decide_eq_false e2, Bool.or_false]
    obtain ⟨t1, t3, t7, tl⟩ := tail_has (C.gates.map (rl (rho h n))) _ (n + 6 + C.size) h (h+1) (n+2) (n+3)
      (rho h n (tap 0)) _ _ _ _ _ (by rw [hxlen]; exact hB) (hin h (by omega)) (hin (h+1) (by omega))
      (hin (n+2) (by omega)) (hin (n+3) (by omega)) (hT 0)
    show (wr (tail _ _ _ _ _ _ _) _).getD (if i.val < a+1 then rho h n (tap (Fin.ofNat (a+1) i.val))
      else if i.val = a+1 then n + 6 + C.size + 1 else if i.val = a+2 then n + 6 + C.size + 3
      else n + 6 + C.size + 7) false = (if i.val < a+1 then W (ret h n l.val) (Fin.ofNat (a+1) i.val)
      else if i.val = a+1 then decide (h+1 ≤ l.val ∧ l.val < n+3)
      else if i.val = a+2 then decide (h+2 ≤ l.val ∧ l.val < n+4)
      else if l.val = h+1 then false else if l.val = n+3 then true else W (ret h n l.val) 0)
    by_cases c0 : i.val < a + 1
    · rw [if_pos c0, if_pos c0]
      exact (tl _ _ (hT _)).2
    rw [if_neg c0, if_neg c0]
    by_cases c1 : i.val = a + 1
    · rw [if_pos c1, if_pos c1, t1.2]
      by_cases d1 : h < l.val <;> by_cases d2 : n + 2 < l.val <;> simp [d1, d2] <;> omega
    rw [if_neg c1, if_neg c1]
    by_cases c2 : i.val = a + 2
    · rw [if_pos c2, if_pos c2, t3.2]
      by_cases d1 : h + 1 < l.val <;> by_cases d2 : n + 3 < l.val <;> simp [d1, d2] <;> omega
    rw [if_neg c2, if_neg c2, t7.2]
    by_cases c3 : l.val = h + 1
    · have a1 : h < l.val := by omega
      have a2 : ¬ (h + 1 < l.val) := by omega
      simp [a1, a2, c3]
    rw [if_neg c3]
    by_cases c4 : l.val = n + 3
    · have a1 : h < l.val := by omega
      have a2 : h + 1 < l.val := by omega
      have a3 : n + 2 < l.val := by omega
      have a4 : ¬ (n + 3 < l.val) := by omega
      rw [if_pos c4]
      simp [a1, a2, a3, a4]
    rw [if_neg c4]
    by_cases c5 : l.val ≤ h
    · have a1 : ¬ (h < l.val) := by omega
      have a3 : ¬ (n + 2 < l.val) := by omega
      simp [a1, a3]
    by_cases c6 : l.val ≤ n + 2
    · have a1 : h < l.val := by omega
      have a2 : h + 1 < l.val := by omega
      have a3 : ¬ (n + 2 < l.val) := by omega
      have a4 : ¬ (n + 3 < l.val) := by omega
      simp [a1, a2, a3, a4]
    · have a1 : h < l.val := by omega
      have a2 : h + 1 < l.val := by omega
      have a3 : n + 2 < l.val := by omega
      have a4 : n + 3 < l.val := by omega
      have e : ret h n l.val = n := by unfold ret; split_ifs <;> omega
      rw [e, hWn]
      simp [a1, a2, a3, a4]

theorem Fit.re {n a p b s : ℕ} {W : ℕ → Fin a → Bool} (hf : Fit n a p b s W) {n' a' p' b' s' : ℕ}
    (V : ℕ → Fin a' → Bool) (hn : n' = n) (hp : p ≤ p') (hb : b ≤ b') (hs : s ≤ s')
    (f : Fin a' → Fin a) (hV : ∀ l ≤ n, ∀ i, V l i = W l (f i)) : Fit n' a' p' b' s' V := by
  subst hn
  obtain ⟨C, tap, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hf
  exact ⟨C, fun i => tap (f i), h1, h2, h3, fun i => h4 _, by omega, by omega, by omega,
    fun l i => by rw [hV l.val (by have := l.isLt; omega) i]; exact h8 l (f i)⟩

theorem base : Fit 2 2 1 1 2 (fun (l : ℕ) (_ : Fin 2) => decide (l = 1)) := by
  refine ⟨⟨[] ++ [gN 1] ++ [gA 0 4], 0⟩, fun _ => 5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact F2_A _ _ (F2_N _ (fun g hg => absurd hg (by simp)))
  · exact rb_snoc _ (rb_snoc _ (fun j hj => absurd hj (by simp)) (by simp [gN])) (by simp [gA])
  · decide
  · intro _; show (5 : ℕ) < 2 + 2 + 2; omega
  · decide
  · decide
  · decide
  · intro l i
    fin_cases l <;> revert i <;> decide

theorem part2 : ∀ h : ℕ, Fit (2*(2*h+1)) (2*h+1+1) (5*h+1) (3*h+1) (8*h+2)
    (fun (l : Nat) (i : Fin (2*h+1+1)) =>
      if i.val = 0 then decide (l % 2 = 1) else decide (i.val ≤ l ∧ l < 2*h+1+i.val)) := by
  intro h
  induction h with
  | zero =>
    refine base.re _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun i => ⟨i.val, by have := i.isLt; omega⟩) ?_
    intro l hl i
    have := i.isLt
    show (if i.val = 0 then decide (l % 2 = 1) else decide (i.val ≤ l ∧ l < 2*0+1+i.val))
      = decide (l = 1)
    split_ifs <;> exact decide_eq_decide.mpr (by omega)
  | succ h ih =>
    have e := part1 (2*(2*h+1)) (2*h+1) (5*h+1) (3*h+1) (8*h+2) (2*h+1) _ (by omega)
      (by simp only [Fin.val_zero, ↓reduceIte, decide_eq_false_iff_not]; omega) ih
    refine e.re _ (by omega) (by omega) (by omega) (by omega)
      (fun i => if i.val = 0 then ⟨2*h+1+3, by omega⟩ else ⟨i.val, by have := i.isLt; omega⟩) ?_
    intro l hl i
    have hi := i.isLt
    by_cases c : i.val = 0
    · simp only [c, ↓reduceIte, Fin.val_zero]
      unfold ret
      split_ifs <;>
        first
          | omega
          | exact decide_eq_false (by omega)
          | exact decide_eq_true (by omega)
          | exact decide_eq_decide.mpr (by omega)
    · by_cases c1 : i.val < 2*h+1+1
      · have hm : (Fin.ofNat (2*h+1+1) i.val).val = i.val := Nat.mod_eq_of_lt c1
        simp only [c, c1, hm, ↓reduceIte]
        unfold ret
        split_ifs <;>
          first
            | omega
            | exact decide_eq_false (by omega)
            | exact decide_eq_true (by omega)
            | exact decide_eq_decide.mpr (by omega)
      · simp only [c, c1, ↓reduceIte]
        split_ifs <;>
          first
            | omega
            | exact decide_eq_false (by omega)
            | exact decide_eq_true (by omega)
            | exact decide_eq_decide.mpr (by omega)

end PEqualNP.Outside.L_lib_1385

open PEqualNP.Outside.L_lib_1385

theorem PEqualNP.Outside.L_lib_1385 :
  let fit := fun (n a p b s : Nat) (W : Nat → Fin a → Bool) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧ (∀ i, tap i < n+2+C.size) ∧
      C.size - PEqualNP.NotBracket.notCount C ≤ p ∧ PEqualNP.NotBracket.notCount C ≤ b ∧ C.size ≤ s ∧
      ∀ (l : Fin (n+1)) i, (C.wires
        (List.ofFn (fun j : Fin n => decide (j.val < l.val)) ++ [false,true])).getD (tap i) false = W l.val i
  (∀ (n a p b s h : Nat) (W : Nat → Fin (a+1) → Bool),
    h < n → W h 0 = true → W n 0 = false → fit n (a+1) p b s W →
    let retime := fun l : Nat => if l ≤ h then l else min n (max h (l-2))
    let V := fun (l : Nat) (i : Fin (a+4)) =>
      if i.val < a+1 then W (retime l) (Fin.ofNat (a+1) i.val)
      else if i.val = a+1 then decide (h+1 ≤ l ∧ l < n+3)
      else if i.val = a+2 then decide (h+2 ≤ l ∧ l < n+4)
      else if l = h+1 then false else if l = n+3 then true else W (retime l) 0
    fit (n+4) (a+4) (p+5) (b+3) (s+8) V) ∧
  ∀ h : Nat,
    let d := 2*h+1
    let V := fun (l : Nat) (i : Fin (d+1)) =>
      if i.val = 0 then decide (l % 2 = 1) else decide (i.val ≤ l ∧ l < d+i.val)
    fit (2*d) (d+1) (5*h+1) (3*h+1) (8*h+2) V := by
  intro fit
  exact ⟨fun n a p b s h W hh _ h2 hf => part1 n a p b s h W hh h2 hf, part2⟩
