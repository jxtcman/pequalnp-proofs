import Mathlib.Tactic
import PEqualNP.Defs

/- The namespace P1297 below is the helper body of the accepted proof L-lib-1297, pasted unchanged. -/
namespace PEqualNP.Outside.L_lib_1367
namespace P1297
section WireFacts
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
variable {n m : ℕ}
abbrev Col (m : ℕ) := Fin m → Bool
noncomputable def raw (x : Fin m → Finset (Fin n)) (i : Fin m) :=
  List.ofFn (fun a : Fin n => decide (a ∈ x i)) ++ [false,true]
noncomputable def val (x : Fin m → Finset (Fin n)) (gs : List Gate) (p : ℕ) : Col m :=
  fun i => ((Circuit.mk gs 0).wires (raw x i)).getD p false
noncomputable def ix (gs : List Gate) := (List.range gs.length).filter fun j =>
  decide ((gs.getD j ⟨.or,[]⟩).op = GateOp.not)
noncomputable def trace (x : Fin m → Finset (Fin n)) (gs : List Gate) :=
  (ix gs).map fun j => val x gs (n+2+j)
noncomputable def sing (x : Fin m → Finset (Fin n)) (a : Fin n) : Col m := fun i => decide (a∈x i)
noncomputable def base (x : Fin m → Finset (Fin n)) : Set (Col m) :=
  {f | f=(fun _ => false) ∨ f=(fun _ => true) ∨ ∃ a, f=sing x a}
noncomputable def inv (f : Col m) : Col m := fun i => !(f i)
noncomputable def conj (f g : Col m) : Col m := fun i => f i && g i
noncomputable def disj (f g : Col m) : Col m := fun i => f i || g i

theorem wirelen (gs : List Gate) (u : List Bool) : ((Circuit.mk gs 0).wires u).length=u.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih => simpa [Circuit.wires,List.foldl_append,Nat.add_assoc] using congrArg Nat.succ ih

theorem old (x : Fin m → Finset (Fin n)) (gs : List Gate) (g : Gate) {p} (hp : p<n+2+gs.length) :
    val x (gs++[g]) p=val x gs p := by
  funext i
  have len := wirelen gs (raw x i)
  rw [show (raw x i).length=n+2 by simp [raw]] at len
  simp only [val,Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil]
  change (((Circuit.mk gs 0).wires (raw x i)) ++ [_]).getD p false = _
  exact List.getD_append _ _ _ _ (by omega)

theorem fresh (x : Fin m → Finset (Fin n)) (gs : List Gate) (g : Gate) (i : Fin m) :
    val x (gs++[g]) (n+2+gs.length) i=g.op.eval (g.inputs.map fun p => val x gs p i) := by
  have len := wirelen gs (raw x i)
  rw [show (raw x i).length=n+2 by simp [raw]] at len
  simp only [val,Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil]
  change ( ((Circuit.mk gs 0).wires (raw x i)) ++ [_]).getD _ false = _
  rw [←len,List.getD_append_right _ _ _ _ (by omega)]
  simp

theorem ixAdd (gs : List Gate) (g : Gate) :
    ix (gs++[g])=ix gs ++ (if g.op=.not then [gs.length] else []) := by
  unfold ix
  simp only [List.length_append,List.length_singleton,List.range_succ,List.filter_append]
  congr 1
  · apply List.filter_congr
    intro i hi
    rw [List.getD_append _ _ _ _ (List.mem_range.mp hi)]
  · by_cases h : g.op=.not <;> simp [h]

theorem ixRange {gs : List Gate} {j} (h : j∈ix gs) : j<gs.length :=
  List.mem_range.mp (List.mem_filter.mp h).1

theorem traceAdd (x : Fin m → Finset (Fin n)) (gs : List Gate) (g : Gate) :
    trace x (gs++[g])=trace x gs ++ (if g.op=.not then [val x (gs++[g]) (n+2+gs.length)] else []) := by
  unfold trace
  rw [ixAdd,List.map_append]
  congr 1
  · apply List.map_congr_left
    intro j hj
    exact old _ _ _ (by have := ixRange hj; omega)
  · split <;> rfl

theorem countIx (gs : List Gate) : PEqualNP.NotBracket.notCount ⟨gs,0⟩=(ix gs).length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [ixAdd]
    unfold PEqualNP.NotBracket.notCount at *
    by_cases h : g.op=.not <;> simp [List.filter_append,h,ih]

theorem extendBack (gs : List Gate) (g : Gate) (h : ReadsBack (n+2) ⟨gs,0⟩)
    (ok : ∀ p∈g.inputs,p<n+2+gs.length) : ReadsBack (n+2) ⟨gs++[g],0⟩ := by
  intro j hj p hp
  simp only [List.length_append,List.length_singleton] at hj
  by_cases hj' : j<gs.length
  · apply h j hj' p
    simpa only [gateAt,List.getD_append _ _ _ _ hj'] using hp
  · obtain rfl : j=gs.length := by omega
    apply ok
    simpa [gateAt,List.getD_append_right _ _ _ _ (le_refl _)] using hp

-- A column gives one wire value per sample. Only a physical NOT extends the trace.
noncomputable def Built (x : Fin m → Finset (Fin n)) (tr : List (Col m)) (k : ℕ) (S : Set (Col m)) :=
  ∃ gs : List Gate, FanInTwo ⟨gs,0⟩ ∧ ReadsBack (n+2) ⟨gs,0⟩ ∧ gs.length≤k ∧ trace x gs=tr ∧
    ∀ f∈S, ∃ p<n+2+gs.length, val x gs p=f
end WireFacts

section Compiler
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
variable {n m : ℕ} {x : Fin m → Finset (Fin n)} {tr : List (Col m)} {k : ℕ} {S : Set (Col m)}

theorem Built.start : Built x [] 0 (base x) := by
  refine ⟨[],by simp [FanInTwo],by simp [ReadsBack],by simp,rfl,?_⟩
  intro f hf
  rcases hf with rfl|rfl|⟨a,rfl⟩
  · refine ⟨n,by simp,?_⟩
    funext i
    simp [val,Circuit.wires,raw]
  · refine ⟨n+1,by simp,?_⟩
    funext i
    simp [val,Circuit.wires,raw]
  · refine ⟨a.val,by have := a.isLt; simp; omega,?_⟩
    funext i
    change ((List.ofFn fun u : Fin n => decide (u∈x i)) ++ _).getD a.val false=_
    rw [List.getD_append _ _ _ _ (by simp)]
    simp [sing]

theorem Built.relax {K : ℕ} {T : Set (Col m)} (ih : Built x tr k S) (sz : k≤K) (sub : T⊆S) : Built x tr K T := by
  obtain ⟨gs,fan,back,le,trace,signal⟩ := ih
  exact ⟨gs,fan,back,le.trans sz,trace,fun f hf => signal f (sub hf)⟩

theorem Built.andGate {f z : Col m} (ih : Built x tr k S) (hf : f∈S) (hg : z∈S) : Built x tr (k+1) (insert (conj f z) S) := by
  obtain ⟨gs,fan,back,sz,ht,sig⟩ := ih
  obtain ⟨a,ha,ea⟩ := sig _ hf
  obtain ⟨b,hb,eb⟩ := sig _ hg
  let g : Gate := ⟨.and,[a,b]⟩
  refine ⟨gs++[g],?_,?_,by simpa using sz,?_,?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with oj|nj
    · exact fan j oj
    · obtain rfl : j=g := List.mem_singleton.mp nj
      simp [g]
  · apply extendBack _ _ back
    simp_all [g]
  · rw [traceAdd]; simpa [g] using ht
  · intro f mem
    rcases mem with rfl|mem
    · refine ⟨n+2+gs.length,by simp,?_⟩
      funext i; rw [fresh]; simp [g,GateOp.eval,ea,eb,conj]
    · obtain ⟨p,hp,eq⟩ := sig _ mem
      exact ⟨p,by simp; omega,(old _ _ _ hp).trans eq⟩

theorem Built.orGate {f z : Col m} (ih : Built x tr k S) (hf : f∈S) (hg : z∈S) : Built x tr (k+1) (insert (disj f z) S) := by
  obtain ⟨gs,fan,back,sz,ht,sig⟩ := ih
  obtain ⟨a,ha,ea⟩ := sig _ hf
  obtain ⟨b,hb,eb⟩ := sig _ hg
  let g : Gate := ⟨.or,[a,b]⟩
  refine ⟨gs++[g],?_,?_,by simpa using sz,?_,?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with oj|nj
    · exact fan j oj
    · obtain rfl : j=g := List.mem_singleton.mp nj
      simp [g]
  · apply extendBack _ _ back
    simp_all [g]
  · rw [traceAdd]; simpa [g] using ht
  · intro f mem
    rcases mem with rfl|mem
    · refine ⟨n+2+gs.length,by simp,?_⟩
      funext i; rw [fresh]; simp [g,GateOp.eval,ea,eb,disj]
    · obtain ⟨p,hp,eq⟩ := sig _ mem
      exact ⟨p,by simp; omega,(old _ _ _ hp).trans eq⟩

theorem Built.notGate {f : Col m} (ih : Built x tr k S) (hf : f∈S) : Built x (tr++[inv f]) (k+1) (insert (inv f) S) := by
  obtain ⟨gs,fan,back,sz,ht,sig⟩ := ih
  obtain ⟨a,ha,ea⟩ := sig _ hf
  let g : Gate := ⟨.not,[a]⟩
  have ev : val x (gs++[g]) (n+2+gs.length)=inv f := by
    funext i; rw [fresh]; simp [g,GateOp.eval,ea,inv]
  refine ⟨gs++[g],?_,?_,by simpa using sz,by simp [traceAdd,g,ht,ev],?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with old|new
    · exact fan j old
    · obtain rfl : j=g := List.mem_singleton.mp new
      simp [g]
  · apply extendBack _ _ back; simpa [g] using ha
  · intro f mem
    rcases mem with rfl|mem
    · exact ⟨_,by simp,ev⟩
    · obtain ⟨p,hp,eq⟩ := sig _ mem
      exact ⟨p,by simp; omega,(old _ _ _ hp).trans eq⟩

end Compiler

section Construction
open scoped Classical
variable {n m : ℕ} {x : Fin m → Finset (Fin n)} {tr : List (Col m)} {k : ℕ} {S : Set (Col m)}

noncomputable def Grow (x : Fin m → Finset (Fin n)) (tr : List (Col m)) (k : ℕ) (S : Set (Col m))
    (b : ℕ) (f : Col m) := ∃ T, Built x tr (k+b) T ∧ S⊆T ∧ f∈T

theorem batch {ι : Type} (s : Finset ι) (F : ι → Col m) (b : ℕ) (H : Built x tr k S)
    (make : ∀ {K T}, Built x tr K T → S⊆T → ∀ a∈s, Grow x tr K T b (F a)) :
    ∃ T, Built x tr (k+s.card*b) T ∧ S⊆T ∧ ∀ a∈s, F a∈T := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨S,by simpa using H,Set.Subset.rfl,by simp⟩
  | @insert a s fresh ih =>
    obtain ⟨U,hU,sub,allU⟩ := ih (fun h st i hi => make h st i (Finset.mem_insert_of_mem hi))
    obtain ⟨T,hT,ut,hit⟩ := make hU sub a (Finset.mem_insert_self _ _)
    refine ⟨T,by simpa [Finset.card_insert_of_notMem fresh,Nat.add_mul,Nat.add_assoc] using hT,sub.trans ut,?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hh
    · exact hit
    · exact ut (allU _ hh)

theorem allFold {ι : Type} (s : Finset ι) (F : ι → Col m) (H : Built x tr k S)
    (unit : (fun _ => true)∈S) (get : ∀ a∈s, F a∈S) :
    Grow x tr k S s.card (fun j => decide (∀ a∈s, F a j=true)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨S,by simpa using H,Set.Subset.rfl,by simpa using unit⟩
  | @insert a s fr ih =>
    obtain ⟨T,h,st,ft⟩ := ih (fun a ha => get a (Finset.mem_insert_of_mem ha))
    have g := Built.andGate h (st (get a (Finset.mem_insert_self _ _))) ft
    refine ⟨_,by simpa [Finset.card_insert_of_notMem fr,Nat.add_assoc] using g,st.trans (Set.subset_insert _ _),?_⟩
    apply Set.mem_insert_iff.mpr; left
    funext j
    simp [conj, Bool.decide_and]

theorem anyFold {ι : Type} (s : Finset ι) (F : ι → Col m) (H : Built x tr k S)
    (unit : (fun _ => false)∈S) (get : ∀ a∈s, F a∈S) :
    Grow x tr k S s.card (fun j => decide (∃ a∈s, F a j=true)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨S,by simpa using H,Set.Subset.rfl,by simpa using unit⟩
  | @insert a s fr ih =>
    obtain ⟨T,h,st,ft⟩ := ih (fun a ha => get a (Finset.mem_insert_of_mem ha))
    have g := Built.orGate h (st (get a (Finset.mem_insert_self _ _))) ft
    refine ⟨_,by simpa [Finset.card_insert_of_notMem fr,Nat.add_assoc] using g,st.trans (Set.subset_insert _ _),?_⟩
    apply Set.mem_insert_iff.mpr; left
    funext j
    simp [disj, Bool.decide_or]

-- A surviving sample must be contained in the current mask and agree on the processed bits.
noncomputable def indicator (x : Fin m → Finset (Fin n)) (v : Fin m → ℕ) (i : Fin m) : Col m :=
  fun j => decide (x i⊆x j ∧ v i=v j)
noncomputable def hist (r : ℕ) (v : Fin m → ℕ) : List (Col m) :=
  List.ofFn fun b : Fin r => fun i => !(v i).testBit (r-1-b.val)

theorem hist_succ (r : ℕ) (v : Fin m → ℕ) :
    hist (r+1) v=hist r (fun i => v i/2) ++ [fun i => !(v i).testBit 0] := by
  rw [hist,List.ofFn_succ',List.concat_eq_append]
  congr 1
  · unfold hist
    congr 1
    funext b i
    simp [Nat.testBit_div_two,show r-1-(b:ℕ)+1 = r+1-1-b by have := b.isLt; omega]
  · simp

theorem stages (x : Fin m → Finset (Fin n)) (r : ℕ) (v : Fin m → ℕ)
    (cap : ∀ i, v i<2^r) (mono : ∀ i j, x i⊆x j → v i≤v j) :
    ∃ S, Built x (hist r v) (m*(n+2*r)+r) S ∧ base x ⊆ S ∧ ∀ i, indicator x v i∈S := by
  induction r generalizing v with
  | zero =>
    have z : ∀ i,v i=0 := fun i => by have := cap i; simp at this; omega
    obtain ⟨T,bt,st,allT⟩ := batch (Finset.univ : Finset (Fin m)) (indicator x v) n (Built.start (x:=x)) (by
      intro K U h bu i _
      obtain ⟨V,hh,sub,fi⟩ := allFold (x i) (sing x) h (bu (Or.inr (Or.inl rfl)))
        (fun a _ => bu (Or.inr (Or.inr ⟨a,rfl⟩)))
      have lim := Finset.card_le_univ (x i)
      refine ⟨V,hh.relax (by simpa using Nat.add_le_add_left lim K) Set.Subset.rfl,sub,?_⟩
      have eq : indicator x v i = (fun j => decide (∀ a ∈ x i,sing x a j=true)) := by
        funext j; simp [indicator,sing,z,Finset.subset_iff]
      rw [eq]; convert fi using 1; funext j; apply Bool.eq_iff_iff.mpr; simp)
    exact ⟨T,by simpa [hist] using bt,st,fun i => allT i (Finset.mem_univ _)⟩
  | succ r ih =>
    let u := fun i => v i/2
    have ucap : ∀ i,u i<2^r := fun i => by have := cap i; simp [pow_succ] at this; dsimp [u]; omega
    obtain ⟨S,h,bs,hInd⟩ := ih u ucap (fun i j h => Nat.div_le_div_right (mono i j h))
    let bit : Col m := fun i => (v i).testBit 0
    let sel := Finset.univ.filter fun i => bit i=true
    obtain ⟨T,hT,st,hit⟩ := anyFold sel (indicator x u) h (bs (Or.inl rfl)) (fun i _ => hInd i)
    have eqn : (fun j => decide (∃ a∈sel, indicator x u a j=true))=bit := by
      funext j
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,indicator,sel,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨a,ba,sub,eq⟩
        have ord := mono a j sub
        simp [u] at eq
        simp [bit] at ba ⊢
        omega
      · intro b; exact ⟨j,b,Finset.Subset.rfl,rfl⟩
    have hit2 : bit ∈ T := by
      rw [←eqn]; convert hit using 1; funext j; apply Bool.eq_iff_iff.mpr; simp
    have hn := Built.notGate hT hit2
    let U := insert (inv bit) T
    have su : S⊆U := st.trans (Set.subset_insert _ _)
    obtain ⟨V,hV,uv,allV⟩ := batch (Finset.univ : Finset (Fin m)) (indicator x v) 1 hn (by
      intro K W hw uw i _
      have iw := uw (su (hInd i))
      by_cases bi : bit i=true
      · have same : indicator x v i=indicator x u i := by
          funext j; simp only [indicator,decide_eq_decide]
          constructor
          · rintro ⟨a,b⟩; exact ⟨a,congrArg (·/2) b⟩
          · rintro ⟨a,b⟩; have ord := mono i j a
            simp [bit] at bi; dsimp [u] at b; exact ⟨a,by omega⟩
        exact ⟨W,hw.relax (by omega) Set.Subset.rfl,Set.Subset.rfl,same ▸ iw⟩
      · have bw : inv bit ∈ W := uw (Set.mem_insert _ _)
        have made := Built.andGate hw iw bw
        refine ⟨_,made,Set.subset_insert _ _,Set.mem_insert_iff.mpr (Or.inl ?_)⟩
        funext j
        apply Bool.eq_iff_iff.mpr
        simp only [indicator,conj,inv,decide_eq_true_eq,Bool.and_eq_true,Bool.not_eq_true']
        simp [bit] at bi
        simp [bit,u]
        grind)
    have lim : sel.card≤m := by simpa using Finset.card_le_univ sel
    rw [hist_succ]
    refine ⟨V,hV.relax ?_ Set.Subset.rfl,(bs.trans su).trans uv,fun i => allV i (Finset.mem_univ _)⟩
    simp only [Finset.card_univ,Fintype.card_fin,mul_one]
    simp only [Nat.mul_add,Nat.mul_succ] at *
    omega
end Construction

section TraceOrder
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
variable {n m : ℕ} {x : Fin m → Finset (Fin n)}
noncomputable def decode (i : Fin m) : List (Col m) → ℕ
  | [] => 0
  | a::as => 2*decode i as + if a i then 0 else 1
noncomputable def score (i : Fin m) (word : List (Col m)) := decode i word.reverse
theorem snocScore (i : Fin m) (l : List (Col m)) (f : Col m) :
    score i (l++[f])=2*score i l + if f i then 0 else 1 := by simp [score,decode]

theorem other (x : Fin m → Finset (Fin n)) (gs : List Gate) (g : Gate) {p}
    (hp : p≠n+2+gs.length) : val x (gs++[g]) p=val x gs p := by
  by_cases low : p<n+2+gs.length
  · exact old x gs g low
  funext i
  have oz := wirelen gs (raw x i)
  have nz := wirelen (gs++[g]) (raw x i)
  rw [show (raw x i).length=n+2 by simp [raw]] at oz nz
  simp only [List.length_append,List.length_singleton] at nz
  unfold val
  rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]

theorem rawMono {i j : Fin m} (sub : x i ⊆ x j) (p : ℕ) :
    val x [] p i=true → val x [] p j=true := by
  by_cases hp : p<n
  · simp only [val,Circuit.wires,List.foldl_nil,raw]
    rw [List.getD_append _ _ _ _ (by simpa using hp),List.getD_append _ _ _ _ (by simpa using hp)]
    simpa [List.getD_eq_getElem?_getD,hp] using @sub ⟨p,hp⟩
  · simp only [val,Circuit.wires,List.foldl_nil,raw]
    rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hp),
      List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hp)]
    simp

theorem ordinary {i j : Fin m} {gs : List Gate} (prior : ∀ p,val x gs p i=true → val x gs p j=true)
    (g : Gate) (op : g.op=.and ∨ g.op=.or) :
    val x (gs++[g]) (n+2+gs.length) i=true → val x (gs++[g]) (n+2+gs.length) j=true := by
  rw [fresh,fresh]
  rcases op with op|op
  · simp only [op,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
    exact fun h p hp => prior _ (h p hp)
  · simp only [op,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    rintro ⟨p,hp,v⟩; exact ⟨p,hp,prior _ v⟩

theorem inverseGate {i j : Fin m} {gs : List Gate} (prior : ∀ p,val x gs p i=true → val x gs p j=true)
    (g : Gate) (op : g.op=.not) :
    val x (gs++[g]) (n+2+gs.length) j=true → val x (gs++[g]) (n+2+gs.length) i=true := by
  rw [fresh,fresh]
  cases args : g.inputs with
  | nil => simp [op,GateOp.eval]
  | cons a l =>
    have h := prior a
    simp [op,GateOp.eval]
    cases e : val x gs a i <;> cases d : val x gs a j <;> simp_all

theorem stepOrder (x : Fin m → Finset (Fin n)) (gs : List Gate) (fan : FanInTwo ⟨gs,0⟩)
    (i j : Fin m) (sub : x i⊆x j) :
    score i (trace x gs) ≤ score j (trace x gs) ∧
    (score i (trace x gs)=score j (trace x gs) → ∀ p,val x gs p i=true → val x gs p j=true) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨le_refl _,fun _ => rawMono sub⟩
  | append_singleton gs g ih =>
    obtain ⟨le,transfer⟩ := ih (fun u hu => fan u (List.mem_append_left _ hu))
    have ops := (fan g (List.mem_append_right _ (List.mem_singleton_self _))).1
    change g.op=.and ∨ g.op=.or ∨ g.op=.not at ops
    by_cases nt : g.op=.not
    · simp only [traceAdd,ite_eq_left nt,snocScore]
      let p := n+2+gs.length
      by_cases eq : score i (trace x gs)=score j (trace x gs)
      · have ant := inverseGate (transfer eq) g nt
        constructor
        · rw [eq]
          change _ + (if val x (gs++[g]) p i then 0 else 1) ≤ _ + (if val x (gs++[g]) p j then 0 else 1)
          cases ai : val x (gs++[g]) p i <;> cases aj : val x (gs++[g]) p j <;> simp_all [p]
        · intro same a
          by_cases aeq : a=p
          · subst a
            dsimp [p] at *
            split at same <;> split at same <;> simp_all
          · rw [other x gs g aeq]; exact transfer eq _
      · have strict := lt_of_le_of_ne le eq
        split <;> split <;> constructor <;> omega
    · have ao : g.op=.and ∨ g.op=.or := ops.elim Or.inl (fun h => Or.inr (h.resolve_right nt))
      simp only [traceAdd,ite_eq_right nt,List.append_nil]
      refine ⟨le,fun eq a => ?_⟩
      by_cases he : a=n+2+gs.length
      · subst a; exact ordinary (transfer eq) g ao
      · rw [other x gs g he]; exact transfer eq _
end TraceOrder

section Characterization
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
variable {n m t r : ℕ} (x : Fin m → Finset (Fin n)) (v : Fin m → ℕ) (w : Fin m → Fin t → Bool)

noncomputable def OK := ∀ i j, x i ⊆ x j → v i ≤ v j ∧ (v i=v j → ∀ a,w i a=true → w j a=true)
noncomputable def Fits (r : ℕ) (C : Circuit) (tap : Fin t → ℕ) := FanInTwo C ∧ ReadsBack (n+2) C ∧
  C.output<n+2+C.size ∧ PEqualNP.NotBracket.notCount C=r ∧ (ix C.gates).length=r ∧
  (∀ a,tap a<n+2+C.size) ∧ (∀ i a,val x C.gates (tap a) i=w i a) ∧
  ∀ i (b : Fin r),val x C.gates (n+2+(ix C.gates).getD b.val C.size) i= !(v i).testBit (r-1-b.val)

theorem decodeHist (i : Fin m) (r : ℕ) (v : Fin m → ℕ) (cap : ∀ i,v i<2^r) :
    score i (hist r v)=v i := by
  induction r generalizing v with
  | zero => have hi := cap i; simpa [hist,score,decode] using (show 0=v i by simpa using (Nat.eq_zero_of_le_zero (by simpa using hi)).symm)
  | succ r ih =>
    rw [hist_succ,snocScore,ih _ (fun j => by have := cap j; rw [pow_succ] at this; omega)]
    simp [Nat.testBit_zero]
    split <;> omega

theorem traceEq {C : Circuit} {tap : Fin t → ℕ} (fit : Fits x v w r C tap) :
    trace x C.gates=hist r v := by
  obtain ⟨_,_,_,_,len,_,_,allBits⟩ := fit
  apply List.ext_getElem
  · simp [trace,hist,len]
  · intro j hj hj'
    have h : j<r := by simpa [hist] using hj'
    have ht : j<(ix C.gates).length := by omega
    simp only [trace,hist,List.getElem_map,List.getElem_ofFn]
    funext i
    have e := allBits i ⟨j,h⟩
    change val x C.gates (n+2+(ix C.gates).getD j C.size) i=_ at e
    rw [List.getD_eq_getElem _ _ ht] at e
    simpa only [trace,hist,List.getElem_map,List.getElem_ofFn] using e

theorem necessary (cap : ∀ i,v i<2^r) {C tap} (fit : Fits x v w r C tap) : OK x v w := by
  have e := traceEq x v w fit
  intro i j sub
  have h := stepOrder x C.gates fit.1 i j sub
  rw [e,decodeHist i r v cap,decodeHist j r v cap] at h
  refine ⟨h.1,?_⟩
  intro eq a ha
  have taps := fit.2.2.2.2.2.2.1
  rw [←taps i a] at ha
  rw [←taps j a]
  exact h.2 eq _ ha

theorem sufficient (cap : ∀ i,v i<2^r) (ok : OK x v w) :
    ∃ C tap,Fits x v w r C tap ∧ C.size≤m*(n+2*r+t)+r := by
  obtain ⟨S,b,baseSub,ind⟩ := stages x r v cap (fun i j h => (ok i j h).1)
  let f := fun a : Fin t => fun i => w i a
  obtain ⟨T,hT,_,haveTap⟩ := batch (Finset.univ : Finset (Fin t)) f m b (by
    intro K U hu su a _
    let sel := Finset.univ.filter fun i => w i a=true
    obtain ⟨V,hV,uv,got⟩ := anyFold sel (indicator x v) hu (su (baseSub (Or.inl rfl))) (fun i _ => su (ind i))
    have lim : sel.card≤m := by simpa using Finset.card_le_univ sel
    refine ⟨V,hV.relax (by omega) Set.Subset.rfl,uv,?_⟩
    convert got using 1
    funext j
    apply Bool.eq_iff_iff.mpr
    simp only [sel,Finset.mem_filter,Finset.mem_univ,true_and,indicator,decide_eq_true_eq,f]
    constructor
    · intro h; exact ⟨j,h,Finset.Subset.rfl,rfl⟩
    · rintro ⟨i,hit,sub,same⟩; exact (ok i j sub).2 same a hit)
  obtain ⟨gs,fan,back,sz,ht,wire⟩ := hT
  choose tap valid data using fun a => wire _ (haveTap a (Finset.mem_univ _))
  have len := congrArg List.length ht
  simp [trace,hist] at len
  refine ⟨⟨gs,0⟩,tap,⟨fan,back,by simp [Circuit.size],(countIx gs).trans len,len,valid,
    fun i a => congrFun (data a) i,?_⟩,?_⟩
  · intro i b
    have hb : b.val<(ix gs).length := by rw [len]; exact b.isLt
    have e := List.getElem_of_eq ht (i:=b.val) (by simpa [trace] using hb)
    change val x gs (n+2+(ix gs).getD b.val gs.length) i=_
    rw [List.getD_eq_getElem _ _ hb]
    simp only [trace,hist,List.getElem_map,List.getElem_ofFn] at e
    exact congrFun e i
  · change gs.length≤_
    simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_comm] using sz
end Characterization

end P1297

namespace Cut
open P1297
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

/-! ### Scores are below two to the number of NOT gates -/

theorem decodeLt {m : ℕ} (i : Fin m) (l : List (Col m)) : decode i l < 2^l.length := by
  induction l with
  | nil => simp [decode]
  | cons c cs ih =>
    simp only [decode, List.length_cons, pow_succ]
    split <;> omega

theorem scoreLt {m : ℕ} (i : Fin m) (l : List (Col m)) : score i l < 2^l.length := by
  have h := decodeLt i l.reverse
  simpa [score] using h

/-! ### Rank compression -/

theorem compress {n m a : ℕ} (x : Fin m → Finset (Fin n)) (v : Fin m → ℕ) (w : Fin m → Fin a → Bool)
    (B q : ℕ) (ok : OK x v w) (cap : ∀ i, v i < B) (hq : min B (max 1 (min m (n+1))) ≤ q) :
    ∃ v' : Fin m → ℕ, OK x v' w ∧ ∀ i, v' i < q := by
  classical
  by_cases hc : min B m ≤ q
  · refine ⟨fun i => ((Finset.univ.image v).filter (fun z => z < v i)).card, ?_, ?_⟩
    · intro i j sub
      obtain ⟨le, mono⟩ := ok i j sub
      refine ⟨Finset.card_le_card (fun z hz => ?_), fun eq => mono ?_⟩
      · simp only [Finset.mem_filter] at hz ⊢
        exact ⟨hz.1, by omega⟩
      · by_contra ne
        have lt : v i < v j := by omega
        have hlt : ((Finset.univ.image v).filter (fun z => z < v i)).card <
            ((Finset.univ.image v).filter (fun z => z < v j)).card := by
          apply Finset.card_lt_card
          refine ⟨fun z hz => ?_, fun h => ?_⟩
          · simp only [Finset.mem_filter] at hz ⊢
            exact ⟨hz.1, by omega⟩
          · have hmem : v i ∈ (Finset.univ.image v).filter (fun z => z < v j) := by
              simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
              exact ⟨⟨i, rfl⟩, lt⟩
            have := h hmem
            simp only [Finset.mem_filter] at this
            omega
        have eq' : ((Finset.univ.image v).filter (fun z => z < v i)).card =
            ((Finset.univ.image v).filter (fun z => z < v j)).card := eq
        omega
    · intro i
      have h1 : ((Finset.univ.image v).filter (fun z => z < v i)).card ≤ v i := by
        calc _ ≤ (Finset.range (v i)).card := Finset.card_le_card (fun z hz => by
                simp only [Finset.mem_filter, Finset.mem_range] at hz ⊢; exact hz.2)
          _ = v i := Finset.card_range _
      have h2 : ((Finset.univ.image v).filter (fun z => z < v i)).card < m := by
        calc _ < (Finset.univ.image v).card := Finset.card_lt_card (Finset.filter_ssubset.2
                ⟨v i, by simp, by simp⟩)
          _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_image_le
          _ = m := by simp
      have := cap i
      show ((Finset.univ.image v).filter (fun z => z < v i)).card < q
      omega
  · refine ⟨fun i => (x i).card, ?_, ?_⟩
    · intro i j sub
      refine ⟨Finset.card_le_card sub, fun eq c hc => ?_⟩
      have eq' : (x i).card = (x j).card := eq
      have e : x i = x j := Finset.eq_of_subset_of_card_le sub (by omega)
      have back : x j ⊆ x i := by rw [e]
      exact (ok i j sub).2 (le_antisymm (ok i j sub).1 (ok j i back).1) c hc
    · intro i
      have : (x i).card ≤ n := by simpa using Finset.card_le_univ (x i)
      show (x i).card < q
      omega

/-! ### The level count -/

noncomputable def hh (n m b : ℕ) : ℕ := min b (Nat.log2 (2*(max 1 (min m (n+1)))-1))
noncomputable def qq (n m b : ℕ) : ℕ := min (2^(hh n m b)) (max 1 (min m (n+1)))

theorem logFact (L : ℕ) (hL : 1 ≤ L) : L ≤ 2^(Nat.log2 (2*L-1)) := by
  have h := Nat.lt_log2_self (n := 2*L-1)
  rw [pow_succ] at h
  omega

theorem hh_le (n m b : ℕ) : hh n m b ≤ b := Nat.min_le_left _ _
theorem qq_le (n m b : ℕ) : qq n m b ≤ 2^(hh n m b) := Nat.min_le_left _ _
theorem qq_pos (n m b : ℕ) : 1 ≤ qq n m b := by
  unfold qq
  have : 1 ≤ 2^(hh n m b) := Nat.one_le_two_pow
  omega
theorem qq_ge (n m b : ℕ) : min (2^b) (max 1 (min m (n+1))) ≤ qq n m b := by
  unfold qq hh
  have hL := logFact (max 1 (min m (n+1))) (le_max_left _ _)
  rcases le_total b (Nat.log2 (2*(max 1 (min m (n+1)))-1)) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    omega

/-! ### Cut pieces -/

noncomputable def arc (x y : Bool) (k : ℕ) : ℕ :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  if x = true ∧ y = false then k else 0

theorem arc_zero {x y : Bool} (k : ℕ) (h : x = true → y = true) : arc x y k = 0 := by
  unfold arc
  cases x <;> cases y <;> simp_all

theorem arc_self (x : Bool) (k : ℕ) : arc x x k = 0 := arc_zero k id

theorem arc_imp {x y : Bool} {K : ℕ} (h : arc x y K < K) : x = true → y = true := by
  unfold arc at h
  cases x <;> cases y <;> simp_all

section Pieces
variable {n m a : ℕ} (mask : Fin m → Finset (Fin n))
  (unary : Fin m → Fin a → Bool → ℕ) (pair : Fin m → Fin a → Fin a → ℕ)

noncomputable def bs (t : Fin m) (v : Bool) : ℕ := ∑ i : Fin a, unary t i v

noncomputable def price (t : Fin m) (w : Fin a → Bool) : ℕ :=
  (∑ i : Fin a, unary t i (w i)) + ∑ i : Fin a, ∑ j : Fin a, arc (w i) (w j) (pair t i j)

noncomputable def offset (q : ℕ) : ℕ := (q-1) * ∑ t : Fin m, (bs unary t false + bs unary t true)

noncomputable def big (q : ℕ) : ℕ := 1 + offset unary q + ∑ t : Fin m, bs unary t false

noncomputable def plain (t : Fin m) (y : Bool) : ℕ :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  if y = true then bs unary t false else bs unary t true

noncomputable def linkT (q : ℕ) (X : Fin m → ℕ → Fin a → Bool) (Y : Fin m → ℕ → Bool)
    (t : Fin m) (r : ℕ) : ℕ :=
  plain unary t (Y t r) + ∑ i : Fin a,
    (arc (Y t r) (X t r i) (big unary q) + arc (X t (r+1) i) (Y t r) (big unary q))

noncomputable def maskT (q : ℕ) (X : Fin m → ℕ → Fin a → Bool) (Y : Fin m → ℕ → Bool)
    (t u : Fin m) : ℕ :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  if mask t ⊆ mask u then
    (∑ r ∈ Finset.range q, ∑ i : Fin a, arc (X t r i) (X u r i) (big unary q)) +
    ∑ r ∈ Finset.range (q-1), arc (Y t r) (Y u r) (big unary q) else 0

noncomputable def lv (q : ℕ) (X : Fin m → ℕ → Fin a → Bool) (t : Fin m) : ℕ :=
  ∑ r ∈ Finset.range q, price unary pair t (X t r)

noncomputable def rowT (q : ℕ) (X : Fin m → ℕ → Fin a → Bool) (Y : Fin m → ℕ → Bool)
    (t : Fin m) : ℕ :=
  lv unary pair q X t + (∑ r ∈ Finset.range (q-1), linkT unary q X Y t r) +
    ∑ u : Fin m, maskT mask unary q X Y t u

noncomputable def cut (q : ℕ) (X : Fin m → ℕ → Fin a → Bool) (Y : Fin m → ℕ → Bool) : ℕ :=
  ∑ t : Fin m, rowT mask unary pair q X Y t

noncomputable def Fit (b : ℕ) (k : ℕ) (C : Circuit) (tap : Fin a → ℕ) : Prop :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  FanInTwo C ∧ ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ (∀ i, tap i < n+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
    (∑ t : Fin m, price unary pair t (fun i => (C.wires
      (List.ofFn (fun j : Fin n => decide (j ∈ mask t)) ++ [false,true])).getD (tap i) false)) ≤ k

noncomputable def Feas (q k : ℕ) : Prop :=
  ∃ (v : Fin m → ℕ) (w : Fin m → Fin a → Bool),
    OK mask v w ∧ (∀ i, v i < q) ∧ (∑ t : Fin m, price unary pair t (w t)) ≤ k

noncomputable def Legal (q : ℕ) (X : Fin m → ℕ → Fin a → Bool) (Y : Fin m → ℕ → Bool) : Prop :=
  (∀ t r, r < q-1 → ∀ i, Y t r = true → X t r i = true) ∧
  (∀ t r, r < q-1 → ∀ i, X t (r+1) i = true → Y t r = true) ∧
  (∀ t u, mask t ⊆ mask u → ∀ r, r < q → ∀ i, X t r i = true → X u r i = true) ∧
  (∀ t u, mask t ⊆ mask u → ∀ r, r < q-1 → Y t r = true → Y u r = true)

theorem price_const (t : Fin m) (c : Bool) : price unary pair t (fun _ => c) = bs unary t c := by
  simp [price, bs, arc_self]

theorem sle {ι : Type} (s : Finset ι) (f : ι → ℕ) {i : ι} (h : i ∈ s) : f i ≤ ∑ j ∈ s, f j :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) h

theorem sumA (v d A P B : ℕ) :
    ∑ r ∈ Finset.range (v+1+d), (if r < v then A else if r = v then P else B) = v*A + P + d*B := by
  induction d with
  | zero =>
    rw [Nat.add_zero, Finset.sum_range_succ, Finset.sum_congr rfl (g := fun _ => A)
      (fun r hr => ite_eq_left (Finset.mem_range.1 hr))]
    simp [mul_comm]
  | succ d ih =>
    rw [← Nat.add_assoc, Finset.sum_range_succ, ih, ite_eq_right (by omega), ite_eq_right (by omega)]
    ring

theorem sumB (v d A B : ℕ) :
    ∑ r ∈ Finset.range (v+d), (if r < v then A else B) = v*A + d*B := by
  induction d with
  | zero =>
    rw [Nat.add_zero, Finset.sum_congr rfl (g := fun _ => A)
      (fun r hr => ite_eq_left (Finset.mem_range.1 hr))]
    simp [mul_comm]
  | succ d ih =>
    rw [← Nat.add_assoc, Finset.sum_range_succ, ih, ite_eq_right (by omega)]
    ring

theorem plain_decide (t : Fin m) (p : Prop) [Decidable p] :
    plain unary t (decide p) = if p then bs unary t false else bs unary t true := by
  unfold plain
  by_cases h : p <;> simp [h]

theorem rowSum (t : Fin m) (Xt : ℕ → Fin a → Bool) (Yt : ℕ → Bool) (v q : ℕ) (hv : v < q)
    (S1 : ∀ r, r < v → Xt r = fun _ => true)
    (S2 : ∀ r, v < r → r < q → Xt r = fun _ => false)
    (S3 : ∀ r, r < q-1 → Yt r = decide (r < v)) :
    (∑ r ∈ Finset.range q, price unary pair t (Xt r)) +
      (∑ r ∈ Finset.range (q-1), plain unary t (Yt r)) =
    (q-1) * (bs unary t false + bs unary t true) + price unary pair t (Xt v) := by
  obtain ⟨d, rfl⟩ : ∃ d, q = v+1+d := ⟨q-v-1, by omega⟩
  have e : v+1+d-1 = v+d := by omega
  rw [e] at S3 ⊢
  rw [Finset.sum_congr rfl (g := fun r => if r < v then bs unary t true else
        if r = v then price unary pair t (Xt v) else bs unary t false) (by
      intro r hr
      have hr' := Finset.mem_range.1 hr
      by_cases h1 : r < v
      · rw [ite_eq_left h1, S1 r h1, price_const]
      · by_cases h2 : r = v
        · rw [ite_eq_right h1, ite_eq_left h2, h2]
        · rw [ite_eq_right h1, ite_eq_right h2, S2 r (by omega) hr', price_const]),
    sumA,
    Finset.sum_congr rfl (g := fun r => if r < v then bs unary t false else bs unary t true) (by
      intro r hr
      rw [S3 r (Finset.mem_range.1 hr), plain_decide]),
    sumB]
  ring

theorem cut_ge (q : ℕ) (X : Fin m → ℕ → Fin a → Bool) (Y : Fin m → ℕ → Bool) :
    ∑ t : Fin m, (lv unary pair q X t + ∑ r ∈ Finset.range (q-1), plain unary t (Y t r)) ≤
      cut mask unary pair q X Y := by
  unfold cut
  apply Finset.sum_le_sum
  intro t _
  unfold rowT
  have h : ∑ r ∈ Finset.range (q-1), plain unary t (Y t r) ≤
      ∑ r ∈ Finset.range (q-1), linkT unary q X Y t r := by
    apply Finset.sum_le_sum
    intro r _
    unfold linkT
    exact Nat.le_add_right _ _
  omega

theorem cut_eq (q : ℕ) (X : Fin m → ℕ → Fin a → Bool) (Y : Fin m → ℕ → Bool)
    (L : Legal mask q X Y) :
    cut mask unary pair q X Y =
      ∑ t : Fin m, (lv unary pair q X t + ∑ r ∈ Finset.range (q-1), plain unary t (Y t r)) := by
  obtain ⟨L1, L2, L3, L4⟩ := L
  unfold cut
  apply Finset.sum_congr rfl
  intro t _
  unfold rowT
  have h1 : ∑ r ∈ Finset.range (q-1), linkT unary q X Y t r =
      ∑ r ∈ Finset.range (q-1), plain unary t (Y t r) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' := Finset.mem_range.1 hr
    unfold linkT
    rw [Finset.sum_eq_zero (fun i _ => by
      rw [arc_zero _ (L1 t r hr' i), arc_zero _ (L2 t r hr' i)]; rfl)]
    rfl
  have h2 : ∑ u : Fin m, maskT mask unary q X Y t u = 0 := by
    apply Finset.sum_eq_zero
    intro u _
    unfold maskT
    split_ifs with sub
    · rw [Finset.sum_eq_zero (fun r hr => Finset.sum_eq_zero (fun i _ =>
          arc_zero _ (L3 t u sub r (Finset.mem_range.1 hr) i))),
        Finset.sum_eq_zero (fun r hr => arc_zero _ (L4 t u sub r (Finset.mem_range.1 hr)))]
      rfl
    · rfl
  rw [h1, h2]
  rfl

theorem legal_of_lt (q : ℕ) (X : Fin m → ℕ → Fin a → Bool) (Y : Fin m → ℕ → Bool)
    (lt : cut mask unary pair q X Y < big unary q) : Legal mask q X Y := by
  have ec : cut mask unary pair q X Y = ∑ t : Fin m, rowT mask unary pair q X Y t := rfl
  have row : ∀ t, rowT mask unary pair q X Y t ≤ cut mask unary pair q X Y := fun t =>
    sle Finset.univ (fun t => rowT mask unary pair q X Y t) (Finset.mem_univ t)
  have er : ∀ t, rowT mask unary pair q X Y t = lv unary pair q X t +
      (∑ r ∈ Finset.range (q-1), linkT unary q X Y t r) +
      ∑ u : Fin m, maskT mask unary q X Y t u := fun _ => rfl
  have link : ∀ t r, r < q-1 → linkT unary q X Y t r ≤ cut mask unary pair q X Y := by
    intro t r hr
    have a2 := sle (Finset.range (q-1)) (fun r => linkT unary q X Y t r) (Finset.mem_range.2 hr)
    have a3 := row t
    rw [er t] at a3
    beta_reduce at a2
    omega
  have el : ∀ t r, linkT unary q X Y t r = plain unary t (Y t r) + ∑ i : Fin a,
      (arc (Y t r) (X t r i) (big unary q) + arc (X t (r+1) i) (Y t r) (big unary q)) :=
    fun _ _ => rfl
  have msk : ∀ t u, maskT mask unary q X Y t u ≤ cut mask unary pair q X Y := by
    intro t u
    have a2 := sle Finset.univ (fun u => maskT mask unary q X Y t u) (Finset.mem_univ u)
    have a3 := row t
    rw [er t] at a3
    beta_reduce at a2
    omega
  have em : ∀ t u, mask t ⊆ mask u → maskT mask unary q X Y t u =
      (∑ r ∈ Finset.range q, ∑ i : Fin a, arc (X t r i) (X u r i) (big unary q)) +
      ∑ r ∈ Finset.range (q-1), arc (Y t r) (Y u r) (big unary q) := by
    intro t u sub
    unfold maskT
    exact ite_eq_left sub
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t r hr i
    have a1 := sle Finset.univ (fun i : Fin a =>
      arc (Y t r) (X t r i) (big unary q) + arc (X t (r+1) i) (Y t r) (big unary q))
      (Finset.mem_univ i)
    have a2 := link t r hr
    rw [el t r] at a2
    beta_reduce at a1
    exact arc_imp (K := big unary q) (by omega)
  · intro t r hr i
    have a1 := sle Finset.univ (fun i : Fin a =>
      arc (Y t r) (X t r i) (big unary q) + arc (X t (r+1) i) (Y t r) (big unary q))
      (Finset.mem_univ i)
    have a2 := link t r hr
    rw [el t r] at a2
    beta_reduce at a1
    exact arc_imp (K := big unary q) (by omega)
  · intro t u sub r hr i
    have a1 := sle Finset.univ (fun i : Fin a => arc (X t r i) (X u r i) (big unary q))
      (Finset.mem_univ i)
    have a2 := sle (Finset.range q) (fun r => ∑ i : Fin a, arc (X t r i) (X u r i) (big unary q))
      (Finset.mem_range.2 hr)
    have a3 := msk t u
    rw [em t u sub] at a3
    beta_reduce at a1 a2
    exact arc_imp (K := big unary q) (by omega)
  · intro t u sub r hr
    have a2 := sle (Finset.range (q-1)) (fun r => arc (Y t r) (Y u r) (big unary q))
      (Finset.mem_range.2 hr)
    have a3 := msk t u
    rw [em t u sub] at a3
    beta_reduce at a2
    exact arc_imp (K := big unary q) (by omega)

theorem firstFalse (N : ℕ) (P : ℕ → Bool) :
    ∃ v, v ≤ N ∧ (∀ r, r < v → P r = true) ∧ (v < N → P v = false) := by
  induction N with
  | zero => exact ⟨0, le_refl _, fun r hr => absurd hr (Nat.not_lt_zero r), fun h => absurd h (Nat.lt_irrefl 0)⟩
  | succ N ih =>
    obtain ⟨v, hv, h1, h2⟩ := ih
    by_cases hlt : v < N
    · exact ⟨v, by omega, h1, fun _ => h2 hlt⟩
    · have hvN : v = N := by omega
      subst hvN
      cases hP : P v with
      | false => exact ⟨v, by omega, h1, fun _ => hP⟩
      | true =>
        refine ⟨v+1, le_refl _, fun r hr => ?_, fun h => absurd h (Nat.lt_irrefl _)⟩
        by_cases hrv : r < v
        · exact h1 r hrv
        · have : r = v := by omega
          rw [this]; exact hP

/-! ### Feasible labelled orders and cuts -/

theorem feas_to_cut (q k : ℕ) (F : Feas mask unary pair q k) :
    ∃ X Y, cut mask unary pair q X Y ≤ offset unary q + k := by
  obtain ⟨v, w, ok, cap, hsum⟩ := F
  let X : Fin m → ℕ → Fin a → Bool := fun t r i =>
    if r < v t then true else if r = v t then w t i else false
  let Y : Fin m → ℕ → Bool := fun t r => decide (r < v t)
  have hXlt : ∀ t r, r < v t → X t r = fun _ => true := by
    intro t r h; funext i; simp only [X]; rw [ite_eq_left h]
  have hXeq : ∀ t, X t (v t) = w t := by
    intro t; funext i; simp [X]
  have hXgt : ∀ t r, v t < r → X t r = fun _ => false := by
    intro t r h; funext i; simp only [X]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have L : Legal mask q X Y := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t r _ i hy
      have h : r < v t := by simpa [Y] using hy
      rw [hXlt t r h]
    · intro t r _ i hx
      by_contra hy
      have h : ¬ r < v t := by simpa [Y] using hy
      rw [hXgt t (r+1) (by omega)] at hx
      exact Bool.false_ne_true hx
    · intro t u sub r _ i hx
      obtain ⟨le, mono⟩ := ok t u sub
      by_cases h1 : r < v t
      · rw [hXlt u r (by omega)]
      · by_cases h2 : r = v t
        · subst h2
          rw [hXeq t] at hx
          by_cases h3 : v t < v u
          · rw [hXlt u _ h3]
          · have e : v t = v u := by omega
            rw [e, hXeq u]
            exact mono e i hx
        · rw [hXgt t r (by omega)] at hx
          exact absurd hx Bool.false_ne_true
    · intro t u sub r _ hy
      have le := (ok t u sub).1
      have h : r < v t := by simpa [Y] using hy
      have h' : r < v u := by omega
      simpa [Y] using h'
  refine ⟨X, Y, ?_⟩
  rw [cut_eq mask unary pair q X Y L]
  have rows : ∀ t ∈ (Finset.univ : Finset (Fin m)),
      lv unary pair q X t + ∑ r ∈ Finset.range (q-1), plain unary t (Y t r) =
      (q-1) * (bs unary t false + bs unary t true) + price unary pair t (w t) := by
    intro t _
    have h := rowSum unary pair t (X t) (Y t) (v t) q (cap t) (hXlt t)
      (fun r hr _ => hXgt t r hr) (fun r _ => rfl)
    rw [hXeq t] at h
    exact h
  rw [Finset.sum_congr rfl rows, Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold offset
  omega

theorem cut_to_feas (q k : ℕ) (hq : 1 ≤ q) (X : Fin m → ℕ → Fin a → Bool) (Y : Fin m → ℕ → Bool)
    (h : cut mask unary pair q X Y ≤ offset unary q + k) : Feas mask unary pair q k := by
  by_cases hk : ∑ t : Fin m, bs unary t false ≤ k
  · refine ⟨fun _ => 0, fun _ _ => false, ?_, fun _ => hq, ?_⟩
    · intro i j _
      exact ⟨le_refl _, fun _ c hc => absurd hc Bool.false_ne_true⟩
    · have e : ∀ t ∈ (Finset.univ : Finset (Fin m)),
          price unary pair t (fun _ => false) = bs unary t false := fun t _ => price_const unary pair t false
      rw [Finset.sum_congr rfl e]
      exact hk
  · have ha : 0 < a := by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · subst h0
        exact absurd (by simp [bs]) hk
      · exact h0
    have lt : cut mask unary pair q X Y < big unary q := by unfold big; omega
    obtain ⟨L1, L2, L3, L4⟩ := legal_of_lt mask unary pair q X Y lt
    choose v hv1 hv2 hv3 using fun t => firstFalse (q-1) (Y t)
    have mono : ∀ t r, v t ≤ r → r < q-1 → Y t r = false := by
      intro t r hr
      induction r, hr using Nat.le_induction with
      | base => exact hv3 t
      | succ r hr ih =>
        intro h1
        have hf := ih (by omega)
        by_contra hy
        have hy' : Y t (r+1) = true := by simpa using hy
        have hx := L1 t (r+1) h1 ⟨0, ha⟩ hy'
        have ht := L2 t r (by omega) ⟨0, ha⟩ hx
        rw [hf] at ht
        exact Bool.false_ne_true ht
    have rows : ∀ t ∈ (Finset.univ : Finset (Fin m)),
        lv unary pair q X t + ∑ r ∈ Finset.range (q-1), plain unary t (Y t r) =
        (q-1) * (bs unary t false + bs unary t true) + price unary pair t (X t (v t)) := by
      intro t _
      have hvt := hv1 t
      refine rowSum unary pair t (X t) (Y t) (v t) q (by omega) ?_ ?_ ?_
      · intro r hr
        funext i
        exact L1 t r (by omega) i (hv2 t r hr)
      · intro r hr hrq
        funext i
        obtain ⟨r', rfl⟩ : ∃ r', r = r'+1 := ⟨r-1, by omega⟩
        have hf := mono t r' (by omega) (by omega)
        by_contra hx
        have hx' : X t (r'+1) i = true := by simpa using hx
        have ht := L2 t r' (by omega) i hx'
        rw [hf] at ht
        exact Bool.false_ne_true ht
      · intro r hr
        by_cases h1 : r < v t
        · rw [hv2 t r h1]; simp [h1]
        · rw [mono t r (by omega) hr]; simp [h1]
    have ge := cut_ge mask unary pair q X Y
    rw [Finset.sum_congr rfl rows, Finset.sum_add_distrib, ← Finset.mul_sum] at ge
    refine ⟨v, fun t => X t (v t), ?_, fun t => by have := hv1 t; omega, ?_⟩
    · intro t u sub
      have hvt := hv1 t
      have hvu := hv1 u
      have le : v t ≤ v u := by
        by_contra hlt
        have h1 : v u < v t := by omega
        have hf := hv3 u (by omega)
        have ht := L4 t u sub (v u) (by omega) (hv2 t (v u) h1)
        rw [hf] at ht
        exact Bool.false_ne_true ht
      refine ⟨le, fun e c hc => ?_⟩
      have e' : v t = v u := e
      have := L3 t u sub (v t) (by omega) c hc
      rw [e'] at this
      exact this
    · show ∑ t : Fin m, price unary pair t (X t (v t)) ≤ k
      unfold offset at h
      omega

end Pieces

/-! ### Circuits and feasible labelled orders -/

section Circ
variable {n m a : ℕ} (mask : Fin m → Finset (Fin n))
  (unary : Fin m → Fin a → Bool → ℕ) (pair : Fin m → Fin a → Fin a → ℕ)

theorem maskEq (i : Fin m) :
    (List.ofFn (fun c : Fin n => @decide (c ∈ mask i) (Classical.propDecidable _)) ++ [false,true])
      = raw mask i := by
  unfold raw
  congr 1
  congr 1
  funext c
  apply Bool.eq_iff_iff.mpr; simp

theorem fitVal (C : Circuit) (tap : Fin a → ℕ) (t : Fin m) :
    (fun i => (C.wires (List.ofFn (fun j : Fin n => @decide (j ∈ mask t) (Classical.propDecidable _))
      ++ [false,true])).getD (tap i) false) = fun i => val mask C.gates (tap i) t := by
  rw [maskEq]
  rfl

theorem circ_to_feas (b k : ℕ) (C : Circuit) (tap : Fin a → ℕ)
    (fit : Fit mask unary pair b k C tap) : Feas mask unary pair (qq n m b) k := by
  obtain ⟨fan, _, _, _, cnt, hsum⟩ := fit
  let v : Fin m → ℕ := fun i => score i (trace mask C.gates)
  let w : Fin m → Fin a → Bool := fun t i => val mask C.gates (tap i) t
  have ok : OK mask v w := by
    intro i j sub
    have h := stepOrder mask C.gates fan i j sub
    exact ⟨h.1, fun eq c hc => h.2 eq _ hc⟩
  have cap : ∀ i, v i < 2^b := by
    intro i
    have h1 := scoreLt i (trace mask C.gates)
    have h2 : (trace mask C.gates).length = PEqualNP.NotBracket.notCount C := by
      rw [show PEqualNP.NotBracket.notCount C = PEqualNP.NotBracket.notCount ⟨C.gates, 0⟩ from rfl,
        countIx]
      simp [trace]
    rw [h2] at h1
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) cnt)
  obtain ⟨v', ok', cap'⟩ := compress mask v w (2^b) (qq n m b) ok cap (qq_ge n m b)
  refine ⟨v', w, ok', cap', ?_⟩
  have e : ∀ t ∈ (Finset.univ : Finset (Fin m)), price unary pair t (w t) =
      price unary pair t (fun i => (C.wires (List.ofFn (fun j : Fin n =>
        @decide (j ∈ mask t) (Classical.propDecidable _)) ++ [false,true])).getD (tap i) false) := by
    intro t _
    rw [fitVal]
  rw [Finset.sum_congr rfl e]
  exact hsum

theorem feas_to_circ (b k : ℕ) (F : Feas mask unary pair (qq n m b) k) :
    ∃ C tap, Fit mask unary pair b k C tap ∧ PEqualNP.NotBracket.notCount C ≤ hh n m b ∧
      C.size ≤ m*(n+2*hh n m b+a)+hh n m b := by
  obtain ⟨v, w, ok, cap, hsum⟩ := F
  have cap' : ∀ i, v i < 2^(hh n m b) := fun i => lt_of_lt_of_le (cap i) (qq_le n m b)
  obtain ⟨C, tap, fits, sz⟩ := sufficient mask v w cap' ok
  obtain ⟨fan, back, out, cnt, _, taps, vals, _⟩ := fits
  refine ⟨C, tap, ⟨fan, back, out, taps, by rw [cnt]; exact hh_le n m b, ?_⟩, le_of_eq cnt, sz⟩
  have e : ∀ t ∈ (Finset.univ : Finset (Fin m)),
      price unary pair t (fun i => (C.wires (List.ofFn (fun j : Fin n =>
        @decide (j ∈ mask t) (Classical.propDecidable _)) ++ [false,true])).getD (tap i) false) =
      price unary pair t (w t) := by
    intro t _
    rw [fitVal]
    congr 1
    funext i
    exact vals t i
  rw [Finset.sum_congr rfl e]
  exact hsum

theorem main (b k : ℕ) :
    ((∃ C tap, Fit mask unary pair b k C tap) ↔
      ∃ X Y, cut mask unary pair (qq n m b) X Y ≤ offset unary (qq n m b) + k) ∧
    ((∃ X Y, cut mask unary pair (qq n m b) X Y ≤ offset unary (qq n m b) + k) →
      ∃ C tap, Fit mask unary pair b k C tap ∧ PEqualNP.NotBracket.notCount C ≤ hh n m b ∧
        C.size ≤ m*(n+2*hh n m b+a)+hh n m b) := by
  have back : (∃ X Y, cut mask unary pair (qq n m b) X Y ≤ offset unary (qq n m b) + k) →
      ∃ C tap, Fit mask unary pair b k C tap ∧ PEqualNP.NotBracket.notCount C ≤ hh n m b ∧
        C.size ≤ m*(n+2*hh n m b+a)+hh n m b := by
    rintro ⟨X, Y, h⟩
    exact feas_to_circ mask unary pair b k
      (cut_to_feas mask unary pair (qq n m b) k (qq_pos n m b) X Y h)
  refine ⟨⟨?_, ?_⟩, back⟩
  · rintro ⟨C, tap, fit⟩
    exact feas_to_cut mask unary pair (qq n m b) k (circ_to_feas mask unary pair b k C tap fit)
  · intro h
    obtain ⟨C, tap, fit, _⟩ := back h
    exact ⟨C, tap, fit⟩

end Circ
end Cut
end PEqualNP.Outside.L_lib_1367

open PEqualNP.Outside.L_lib_1367.Cut

theorem PEqualNP.Outside.L_lib_1367 : letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n m a b : Nat) (mask : Fin m → Finset (Fin n))
    (unary : Fin m → Fin a → Bool → Nat) (pair : Fin m → Fin a → Fin a → Nat),
  let rows : Finset (Fin m) := Finset.univ
  let taps : Finset (Fin a) := Finset.univ
  let limit := max 1 (min m (n+1))
  let h := min b (Nat.log2 (2*limit-1))
  let q := min (2^h) limit
  let levels := Finset.range q
  let links := Finset.range (q-1)
  let arc := fun (x y : Bool) (k : Nat) => if x = true ∧ y = false then k else 0
  let base := fun (t : Fin m) (v : Bool) => taps.sum (fun i => unary t i v)
  let price := fun (t : Fin m) (w : Fin a → Bool) =>
    taps.sum (fun i => unary t i (w i)) +
    taps.sum (fun i => taps.sum (fun j => arc (w i) (w j) (pair t i j)))
  let offset := (q-1) * rows.sum (fun t => base t false + base t true)
  let big := 1 + offset + rows.sum (fun t => base t false)
  let cut := fun (X : Fin m → Nat → Fin a → Bool) (Y : Fin m → Nat → Bool) =>
    rows.sum (fun t =>
      levels.sum (fun r => price t (X t r)) +
      links.sum (fun r =>
        (if Y t r = true then base t false else base t true) +
        taps.sum (fun i => arc (Y t r) (X t r i) big + arc (X t (r+1) i) (Y t r) big)) +
      rows.sum (fun u => if mask t ⊆ mask u then
        levels.sum (fun r => taps.sum (fun i => arc (X t r i) (X u r i) big)) +
        links.sum (fun r => arc (Y t r) (Y u r) big) else 0))
  let fit := fun (k : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ (∀ i, tap i < n+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
    rows.sum (fun t => price t (fun i => (C.wires
      (List.ofFn (fun j : Fin n => decide (j ∈ mask t)) ++ [false,true])).getD (tap i) false)) ≤ k
  ∀ k : Nat,
    ((∃ C tap, fit k C tap) ↔ ∃ X Y, cut X Y ≤ offset+k) ∧
    ((∃ X Y, cut X Y ≤ offset+k) →
      ∃ C tap, fit k C tap ∧ PEqualNP.NotBracket.notCount C ≤ h ∧ C.size ≤ m*(n+2*h+a)+h) := by
  intro n m a b mask unary pair rows taps limit h q levels links arc base price offset big cut fit k
  exact main mask unary pair b k
