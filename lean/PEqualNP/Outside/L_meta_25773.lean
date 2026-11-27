import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25773_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wireV (gs : List Gate) (x : List Bool) (w : ℕ) : Bool :=
  (Circuit.wires ⟨gs, 0⟩ x).getD w false

theorem foldl_stepWire_len (gs : List Gate) :
    ∀ x : List Bool, (gs.foldl stepWire x).length = x.length + gs.length := by
  induction gs with
  | nil => intro x; simp
  | cons g gs ih =>
    intro x
    simp only [List.foldl_cons, List.length_cons, ih, stepWire, List.length_append, List.length_nil]
    omega

theorem wires_len (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length :=
  foldl_stepWire_len gs x

theorem wires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    Circuit.wires ⟨gs ++ [g], 0⟩ x =
      Circuit.wires ⟨gs, 0⟩ x ++
        [g.op.eval (g.inputs.map fun i => wireV gs x i)] := by
  simp [Circuit.wires, List.foldl_append, wireV]

theorem wireV_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    wireV gs x i = x.getD i false := by
  unfold wireV
  change (gs.foldl stepWire x).getD i false = x.getD i false
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (stepWire x g) (by simp [stepWire]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem wireV_append_prefix (gs₁ gs₂ : List Gate) (x : List Bool) (w : ℕ)
    (hw : w < x.length + gs₁.length) :
    wireV (gs₁ ++ gs₂) x w = wireV gs₁ x w := by
  induction gs₂ using List.reverseRecOn with
  | nil => simp [wireV]
  | append_singleton gs₂ g ih =>
    rw [← List.append_assoc, wireV, wires_snoc]
    have hlen : w < (Circuit.wires ⟨gs₁ ++ gs₂, 0⟩ x).length := by
      rw [wires_len, List.length_append]; omega
    rw [List.getD_append _ _ _ _ hlen]
    exact ih

theorem wireV_snoc_new (gs : List Gate) (g : Gate) (x : List Bool) :
    wireV (gs ++ [g]) x (x.length + gs.length) =
      g.op.eval (g.inputs.map fun i => wireV gs x i) := by
  rw [wireV, wires_snoc]
  have hlen : (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := wires_len gs x
  rw [List.getD_eq_getElem _ _ (by simp [hlen]), List.getElem_append_right (by omega)]
  simp [hlen]

def GateOK (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def Ext (_N : ℕ) (gs gs' : List Gate) : Prop :=
  ∃ extra : List Gate, gs' = gs ++ extra ∧ ∀ g ∈ extra, GateOK g

theorem Ext.refl (N : ℕ) (gs : List Gate) : Ext N gs gs :=
  ⟨[], by simp, fun _ h => absurd h List.not_mem_nil⟩

theorem Ext.len_le {N : ℕ} {gs gs' : List Gate} (h : Ext N gs gs') :
    gs.length ≤ gs'.length := by
  obtain ⟨extra, rfl, _⟩ := h
  simp

theorem Ext.trans {N : ℕ} {gs₁ gs₂ gs₃ : List Gate} (h1 : Ext N gs₁ gs₂) (h2 : Ext N gs₂ gs₃) :
    Ext N gs₁ gs₃ := by
  obtain ⟨e1, rfl, ho1⟩ := h1
  obtain ⟨e2, rfl, ho2⟩ := h2
  refine ⟨e1 ++ e2, by simp [List.append_assoc], fun g hg => ?_⟩
  rcases List.mem_append.mp hg with h | h
  · exact ho1 g h
  · exact ho2 g h

theorem Ext.eval {N : ℕ} {gs gs' : List Gate} (h : Ext N gs gs')
    (x : List Bool) (hx : x.length = N) (w : ℕ) (hw : w < N + gs.length) :
    wireV gs' x w = wireV gs x w := by
  obtain ⟨e, rfl, _⟩ := h
  exact wireV_append_prefix gs e x w (by rw [hx]; exact hw)

theorem Ext.fanInTwo {N : ℕ} {gs : List Gate} (h : Ext N [] gs) (out : ℕ) :
    FanInTwo ⟨gs, out⟩ := by
  obtain ⟨e, rfl, ho⟩ := h
  intro g hg
  exact ho g (by simpa using hg)

theorem emitNot (N : ℕ) (gs : List Gate) (a : ℕ) :
    ∃ (gs' : List Gate) (w : ℕ),
      Ext N gs gs' ∧ gs'.length = gs.length + 1 ∧ w < N + gs'.length ∧
      ∀ x : List Bool, x.length = N → wireV gs' x w = !(wireV gs x a) := by
  let g : Gate := ⟨GateOp.not, [a]⟩
  refine ⟨gs ++ [g], N + gs.length, ⟨[g], rfl, fun h hm => by simp at hm; subst hm; exact ⟨by simp [g], by simp [g]⟩⟩,
    by simp, by simp, fun x hx => ?_⟩
  rw [← hx, wireV_snoc_new]
  simp [g, GateOp.eval]

theorem emitAnd (N : ℕ) (gs : List Gate) (a b : ℕ) :
    ∃ (gs' : List Gate) (w : ℕ),
      Ext N gs gs' ∧ gs'.length = gs.length + 1 ∧ w < N + gs'.length ∧
      ∀ x : List Bool, x.length = N → wireV gs' x w = (wireV gs x a && wireV gs x b) := by
  let g : Gate := ⟨GateOp.and, [a, b]⟩
  refine ⟨gs ++ [g], N + gs.length, ⟨[g], rfl, fun h hm => by simp at hm; subst hm; exact ⟨by simp [g], by simp [g]⟩⟩,
    by simp, by simp, fun x hx => ?_⟩
  rw [← hx, wireV_snoc_new]
  simp [g, GateOp.eval]

theorem emitOr (N : ℕ) (gs : List Gate) (a b : ℕ) :
    ∃ (gs' : List Gate) (w : ℕ),
      Ext N gs gs' ∧ gs'.length = gs.length + 1 ∧ w < N + gs'.length ∧
      ∀ x : List Bool, x.length = N → wireV gs' x w = (wireV gs x a || wireV gs x b) := by
  let g : Gate := ⟨GateOp.or, [a, b]⟩
  refine ⟨gs ++ [g], N + gs.length, ⟨[g], rfl, fun h hm => by simp at hm; subst hm; exact ⟨by simp [g], by simp [g]⟩⟩,
    by simp, by simp, fun x hx => ?_⟩
  rw [← hx, wireV_snoc_new]
  simp [g, GateOp.eval]

theorem oneEach_len {n : ℕ} (u v : Fin n) : (oneEach u v).length = n + n := by
  simp [oneEach]

theorem oneEach_getD_left {n : ℕ} (u v : Fin n) {i : ℕ} (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp [hi]),
      List.getD_eq_getElem _ _ (by simp [hi]),
      List.getElem_ofFn]
  simp [Fin.ext_iff]

theorem oneEach_getD_right {n : ℕ} (u v : Fin n) {i : ℕ} (hi : i < n) :
    (oneEach u v).getD (n + i) false = decide (i = v.val) := by
  unfold oneEach
  rw [List.getD_eq_getElem _ _ (by simp; omega),
      List.getElem_append_right (by simp)]
  simp [Fin.ext_iff]

theorem emitDiagChain (n : ℕ) :
    ∀ m : ℕ, 1 ≤ m → m ≤ n →
      ∃ (gs : List Gate) (out : ℕ),
        Ext (n + n) [] gs ∧ gs.length = 2 * m - 1 ∧ out < (n + n) + gs.length ∧
        ∀ (u v : Fin n),
          wireV gs (oneEach u v) out = decide (u = v ∧ u.val < m) := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ k ih =>
    intro _ hkn
    by_cases hk0 : k = 0
    · subst hk0
      obtain ⟨gs, w, he, hlen, hw, hev⟩ := emitAnd (n + n) [] 0 n
      refine ⟨gs, w, he, by simp [hlen], hw, fun u v => ?_⟩
      have hr0 := oneEach_getD_right u v (i := 0) (by omega)
      simp only [Nat.add_zero] at hr0
      rw [hev (oneEach u v) (oneEach_len u v),
          wireV_input [] (oneEach u v) 0 (by rw [oneEach_len]; omega),
          wireV_input [] (oneEach u v) n (by rw [oneEach_len]; omega),
          oneEach_getD_left u v (by omega),
          hr0]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq, Fin.ext_iff]
      omega
    · obtain ⟨gs1, w1, he1, hlen1, hw1, hev1⟩ := ih (by omega) (by omega)
      obtain ⟨gs2, wk, he2, hlen2, hwk, hevk⟩ := emitAnd (n + n) gs1 k (n + k)
      obtain ⟨gs3, w3, he3, hlen3, hw3, hev3⟩ := emitOr (n + n) gs2 w1 wk
      refine ⟨gs3, w3, (he1.trans he2).trans he3, by omega, hw3, fun u v => ?_⟩
      have hlen_in : (oneEach u v).length = n + n := oneEach_len u v
      rw [hev3 (oneEach u v) hlen_in,
          he2.eval (oneEach u v) hlen_in w1 hw1,
          hev1 u v,
          hevk (oneEach u v) hlen_in,
          wireV_input gs1 (oneEach u v) k (by rw [hlen_in]; omega),
          wireV_input gs1 (oneEach u v) (n + k) (by rw [hlen_in]; omega),
          oneEach_getD_left u v (by omega),
          oneEach_getD_right u v (by omega)]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Fin.ext_iff]
      omega

theorem main (n : ℕ) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 2 * n ∧ Represents (fun u v : Fin n => decide (u ≠ v)) C := by
  cases n with
  | zero =>
    refine ⟨⟨[], 0⟩, fun _ h => absurd h List.not_mem_nil, by simp [Circuit.size], fun u => Fin.elim0 u⟩
  | succ m =>
    obtain ⟨gs1, w1, he1, hlen1, _, hev1⟩ := emitDiagChain (m + 1) (m + 1) (by omega) (le_refl _)
    obtain ⟨gs2, w2, he2, hlen2, _, hev2⟩ := emitNot ((m + 1) + (m + 1)) gs1 w1
    refine ⟨⟨gs2, w2⟩, (he1.trans he2).fanInTwo w2, by change gs2.length ≤ 2 * (m + 1); omega, fun u v => ?_⟩
    change wireV gs2 (oneEach u v) w2 = decide (u ≠ v)
    rw [hev2 (oneEach u v) (oneEach_len u v), hev1 u v]
    have hv : v.val < m + 1 := v.isLt
    by_cases huv : u = v
    · simp [huv]; omega
    · simp [huv]

end PEqualNP.Outside.L_meta_25773_aux

theorem PEqualNP.Outside.L_meta_25773 : (∀ (n : ℕ), ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2 * n ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide (u ≠ v)) C) :=
  PEqualNP.Outside.L_meta_25773_aux.main
