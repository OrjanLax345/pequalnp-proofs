import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_488

section GraphHelpers

variable {V : Type*} [DecidableEq V] [Fintype V]

def degIn (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (v : V) : Nat :=
  (U.filter (fun w => G.Adj v w)).card

def StepIn (G : SimpleGraph V) (U : Finset V) (a b : V) : Prop :=
  a ∈ U ∧ b ∈ U ∧ G.Adj a b

def ReachIn (G : SimpleGraph V) (U : Finset V) (a b : V) : Prop :=
  Relation.ReflTransGen (StepIn G U) a b

def ConnIn (G : SimpleGraph V) (U : Finset V) : Prop :=
  ∀ u ∈ U, ∀ v ∈ U, ReachIn G U u v

def Colorable (G : SimpleGraph V) (U : Finset V) (L : V → Finset (Fin 3)) : Prop :=
  ∃ c : V → Fin 3, (∀ v ∈ U, c v ∈ L v) ∧ ∀ u ∈ U, ∀ v ∈ U, G.Adj u v → c u ≠ c v

lemma stepIn_symm {G : SimpleGraph V} {U : Finset V} {a b : V} (h : StepIn G U a b) :
    StepIn G U b a :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

lemma reachIn_symm {G : SimpleGraph V} {U : Finset V} {a b : V} (h : ReachIn G U a b) :
    ReachIn G U b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact Relation.ReflTransGen.head (stepIn_symm hab) ih

lemma reachIn_mono {G : SimpleGraph V} {U₁ U₂ : Finset V} (hsub : U₁ ⊆ U₂) {a b : V}
    (h : ReachIn G U₁ a b) : ReachIn G U₂ a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact Relation.ReflTransGen.tail ih ⟨hsub hab.1, hsub hab.2.1, hab.2.2⟩

lemma degIn_mono {G : SimpleGraph V} [DecidableRel G.Adj] {U₁ U₂ : Finset V} (hsub : U₁ ⊆ U₂) (v : V) :
    degIn G U₁ v ≤ degIn G U₂ v :=
  Finset.card_le_card (Finset.filter_subset_filter _ hsub)

lemma degIn_erase_of_adj {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {v r : V}
    (hr : r ∈ U) (hadj : G.Adj v r) : degIn G (U.erase r) v + 1 = degIn G U v := by
  unfold degIn
  have hmem : r ∈ U.filter (fun w => G.Adj v w) := Finset.mem_filter.mpr ⟨hr, hadj⟩
  have heq : (U.erase r).filter (fun w => G.Adj v w) = (U.filter (fun w => G.Adj v w)).erase r := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_erase]; tauto
  rw [heq, Finset.card_erase_add_one hmem]

lemma degIn_erase_of_not_adj {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {v r : V}
    (hnadj : ¬ G.Adj v r) : degIn G (U.erase r) v = degIn G U v := by
  unfold degIn
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · intro ⟨⟨_, hw⟩, ha⟩; exact ⟨hw, ha⟩
  · intro ⟨hw, ha⟩
    refine ⟨⟨?_, hw⟩, ha⟩
    intro hwr
    subst hwr
    exact hnadj ha

lemma reachIn_erase_or_adj_clean {G : SimpleGraph V} {U : Finset V} {r u v : V}
    (hu : u ∈ U.erase r) (h : ReachIn G U u v) :
    (v ≠ r ∧ ReachIn G (U.erase r) u v) ∨
      ∃ w ∈ U.erase r, ReachIn G (U.erase r) u w ∧ G.Adj w r := by
  induction h with
  | refl => exact Or.inl ⟨(Finset.mem_erase.mp hu).1, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    rcases ih with ⟨hb, h_ub⟩ | hex
    · have hbU : b ∈ U.erase r := Finset.mem_erase.mpr ⟨hb, hbc.1⟩
      by_cases hc : c = r
      · subst hc
        exact Or.inr ⟨b, hbU, h_ub, hbc.2.2⟩
      · exact Or.inl ⟨hc, Relation.ReflTransGen.tail h_ub ⟨hbU, Finset.mem_erase.mpr ⟨hc, hbc.2.1⟩, hbc.2.2⟩⟩
    · exact Or.inr hex

lemma colorable_of_strict_slack {G : SimpleGraph V} [DecidableRel G.Adj] :
    ∀ n : Nat, ∀ (U : Finset V) (L : V → Finset (Fin 3)), U.card = n →
      (∀ v ∈ U, degIn G U v ≤ (L v).card) →
      (∀ u ∈ U, ∃ r ∈ U, ReachIn G U u r ∧ degIn G U r < (L r).card) →
      Colorable G U L := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro U L hcard hdeg hsl
    by_cases hemp : U = ∅
    · subst hemp
      exact ⟨fun _ => 0, fun _ h => (Finset.notMem_empty _ h).elim, fun _ h => (Finset.notMem_empty _ h).elim⟩
    · obtain ⟨u0, hu0⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
      obtain ⟨r, hr, _, hrl⟩ := hsl u0 hu0
      let U' := U.erase r
      have hcard' : U'.card < n := by
        rw [← hcard]
        exact Finset.card_erase_lt_of_mem hr
      have hdeg' : ∀ v ∈ U', degIn G U' v ≤ (L v).card := by
        intro v hv
        exact le_trans (degIn_mono (Finset.erase_subset r U) v) (hdeg v (Finset.mem_of_mem_erase hv))
      have hsl' : ∀ u ∈ U', ∃ r' ∈ U', ReachIn G U' u r' ∧ degIn G U' r' < (L r').card := by
        intro u hu
        obtain ⟨r0, hr0, hreach, hr0l⟩ := hsl u (Finset.mem_of_mem_erase hu)
        rcases reachIn_erase_or_adj_clean hu hreach with ⟨hr0ne, hpath⟩ | ⟨w, hw, hpath, hadj⟩
        · refine ⟨r0, Finset.mem_erase.mpr ⟨hr0ne, hr0⟩, hpath, ?_⟩
          exact lt_of_le_of_lt (degIn_mono (Finset.erase_subset r U) r0) hr0l
        · refine ⟨w, hw, hpath, ?_⟩
          have hde : degIn G U' w + 1 = degIn G U w := degIn_erase_of_adj hr hadj
          have hdw := hdeg w (Finset.mem_of_mem_erase hw)
          omega
      obtain ⟨c', hc'L, hc'adj⟩ := ih U'.card hcard' U' L rfl hdeg' hsl'
      let used := (U'.filter (fun w => G.Adj r w)).image c'
      have hused_le : used.card ≤ degIn G U r := by
        calc used.card ≤ (U'.filter (fun w => G.Adj r w)).card := Finset.card_image_le
          _ = degIn G U' r := rfl
          _ ≤ degIn G U r := degIn_mono (Finset.erase_subset r U) r
      have havail : (L r \ used).Nonempty := by
        apply Finset.card_pos.mp
        have hs := Finset.card_sdiff_add_card_inter (L r) used
        have hi : (L r ∩ used).card ≤ used.card := Finset.card_le_card Finset.inter_subset_right
        omega
      obtain ⟨col, hcol⟩ := havail
      have hcolL : col ∈ L r := (Finset.mem_sdiff.mp hcol).1
      have hcolU : col ∉ used := (Finset.mem_sdiff.mp hcol).2
      refine ⟨Function.update c' r col, ?_, ?_⟩
      · intro v hv
        by_cases hvr : v = r
        · subst hvr; simp [hcolL]
        · rw [Function.update_of_ne hvr]
          exact hc'L v (Finset.mem_erase.mpr ⟨hvr, hv⟩)
      · intro u hu v hv hadj
        by_cases hur : u = r
        · subst hur
          have hvr : v ≠ u := G.ne_of_adj (hadj.symm)
          rw [Function.update_self, Function.update_of_ne hvr]
          intro heq
          apply hcolU
          exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hvr, hv⟩, hadj⟩, heq.symm⟩
        · by_cases hvr : v = r
          · subst hvr
            rw [Function.update_of_ne hur, Function.update_self]
            intro heq
            apply hcolU
            exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hur, hu⟩, hadj.symm⟩, heq⟩
          · rw [Function.update_of_ne hur, Function.update_of_ne hvr]
            exact hc'adj u (Finset.mem_erase.mpr ⟨hur, hu⟩) v (Finset.mem_erase.mpr ⟨hvr, hv⟩) hadj

lemma colorable_of_cherry {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {L : V → Finset (Fin 3)}
    (hdeg : ∀ v ∈ U, degIn G U v ≤ (L v).card)
    {w u₁ u₂ : V} (hw : w ∈ U) (hu₁ : u₁ ∈ U) (hu₂ : u₂ ∈ U)
    (hw₁ : G.Adj w u₁) (hw₂ : G.Adj w u₂) (hne : u₁ ≠ u₂) (hnadj : ¬ G.Adj u₁ u₂)
    (hd₁ : 2 ≤ degIn G U u₁) (hd₂ : 2 ≤ degIn G U u₂)
    (hc : ConnIn G ((U.erase u₁).erase u₂)) : Colorable G U L := by
  classical
  have hinter : (L u₁ ∩ L u₂).Nonempty := by
    apply Finset.card_pos.mp
    have hu := Finset.card_union_add_card_inter (L u₁) (L u₂)
    have hle : (L u₁ ∪ L u₂).card ≤ 3 := by
      simpa using Finset.card_le_univ (L u₁ ∪ L u₂)
    have h1 := le_trans hd₁ (hdeg u₁ hu₁)
    have h2 := le_trans hd₂ (hdeg u₂ hu₂)
    omega
  obtain ⟨c0, hc0⟩ := hinter
  have hc0₁ : c0 ∈ L u₁ := (Finset.mem_inter.mp hc0).1
  have hc0₂ : c0 ∈ L u₂ := (Finset.mem_inter.mp hc0).2
  let U' := (U.erase u₁).erase u₂
  let L' : V → Finset (Fin 3) := fun v =>
    if G.Adj v u₁ ∨ G.Adj v u₂ then (L v).erase c0 else L v
  have hwu₁ : w ≠ u₁ := G.ne_of_adj hw₁
  have hwu₂ : w ≠ u₂ := G.ne_of_adj hw₂
  have hwU' : w ∈ U' := Finset.mem_erase.mpr ⟨hwu₂, Finset.mem_erase.mpr ⟨hwu₁, hw⟩⟩
  have hdeg' : ∀ v ∈ U', degIn G U' v ≤ (L' v).card := by
    intro v hv
    have hv1 : v ∈ U.erase u₁ := Finset.mem_of_mem_erase hv
    have hvU : v ∈ U := Finset.mem_of_mem_erase hv1
    have hdv := hdeg v hvU
    by_cases ha1 : G.Adj v u₁
    · have hd1 := degIn_erase_of_adj hu₁ ha1
      have hd2 : degIn G U' v ≤ degIn G (U.erase u₁) v := degIn_mono (Finset.erase_subset u₂ (U.erase u₁)) v
      have hL' : (L' v).card = ((L v).erase c0).card := by simp [L', ha1]
      have her := Finset.pred_card_le_card_erase (s := L v) (a := c0)
      omega
    · by_cases ha2 : G.Adj v u₂
      · have hu₂' : u₂ ∈ U.erase u₁ := Finset.mem_erase.mpr ⟨hne.symm, hu₂⟩
        have hd2 : degIn G U' v + 1 = degIn G (U.erase u₁) v := degIn_erase_of_adj hu₂' ha2
        have hd1 := degIn_erase_of_not_adj (G := G) (U := U) ha1
        have hL' : (L' v).card = ((L v).erase c0).card := by simp [L', ha2]
        have her := Finset.pred_card_le_card_erase (s := L v) (a := c0)
        omega
      · have hL' : (L' v).card = (L v).card := by simp [L', ha1, ha2]
        have hsub : U' ⊆ U := Finset.Subset.trans (Finset.erase_subset _ _) (Finset.erase_subset _ _)
        have hdm := degIn_mono (G := G) hsub v
        omega
  have hwslack : degIn G U' w < (L' w).card := by
    have hd1 := degIn_erase_of_adj hu₁ hw₁
    have hu₂' : u₂ ∈ U.erase u₁ := Finset.mem_erase.mpr ⟨hne.symm, hu₂⟩
    have hd2 : degIn G U' w + 1 = degIn G (U.erase u₁) w := degIn_erase_of_adj hu₂' hw₂
    have hdw := hdeg w hw
    have hL' : (L' w).card = ((L w).erase c0).card := by simp [L', hw₁]
    have her := Finset.pred_card_le_card_erase (s := L w) (a := c0)
    omega
  have hsl' : ∀ u ∈ U', ∃ r ∈ U', ReachIn G U' u r ∧ degIn G U' r < (L' r).card :=
    fun u hu => ⟨w, hwU', hc u hu w hwU', hwslack⟩
  obtain ⟨c', hc'L, hc'adj⟩ := colorable_of_strict_slack U'.card U' L' rfl hdeg' hsl'
  let c : V → Fin 3 := fun v => if v = u₁ ∨ v = u₂ then c0 else c' v
  refine ⟨c, ?_, ?_⟩
  · intro v hv
    by_cases h1 : v = u₁
    · subst h1; simp [c, hc0₁]
    · by_cases h2 : v = u₂
      · subst h2; simp [c, hc0₂]
      · have hv' : v ∈ U' := Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, hv⟩⟩
        have hmem := hc'L v hv'
        simp only [c, h1, h2, or_self, if_false]
        by_cases ha : G.Adj v u₁ ∨ G.Adj v u₂
        · simp only [L', ha, if_true] at hmem
          exact Finset.mem_of_mem_erase hmem
        · simp only [L', ha, if_false] at hmem
          exact hmem
  · intro a ha b hb hadj
    by_cases ha12 : a = u₁ ∨ a = u₂
    · by_cases hb12 : b = u₁ ∨ b = u₂
      · rcases ha12 with rfl | rfl <;> rcases hb12 with rfl | rfl
        · exact (G.ne_of_adj hadj rfl).elim
        · exact (hnadj hadj).elim
        · exact (hnadj (hadj.symm)).elim
        · exact (G.ne_of_adj hadj rfl).elim
      · have hb1 : b ≠ u₁ := fun h => hb12 (Or.inl h)
        have hb2 : b ≠ u₂ := fun h => hb12 (Or.inr h)
        have hb' : b ∈ U' := Finset.mem_erase.mpr ⟨hb2, Finset.mem_erase.mpr ⟨hb1, hb⟩⟩
        have hba : G.Adj b u₁ ∨ G.Adj b u₂ := by
          rcases ha12 with rfl | rfl
          · exact Or.inl (hadj.symm)
          · exact Or.inr (hadj.symm)
        have hmem := hc'L b hb'
        simp only [L', hba, if_true] at hmem
        simp only [c, ha12, if_true, hb12, if_false]
        exact (Finset.mem_erase.mp hmem).1.symm
    · by_cases hb12 : b = u₁ ∨ b = u₂
      · have ha1 : a ≠ u₁ := fun h => ha12 (Or.inl h)
        have ha2 : a ≠ u₂ := fun h => ha12 (Or.inr h)
        have ha' : a ∈ U' := Finset.mem_erase.mpr ⟨ha2, Finset.mem_erase.mpr ⟨ha1, ha⟩⟩
        have hab : G.Adj a u₁ ∨ G.Adj a u₂ := by
          rcases hb12 with rfl | rfl
          · exact Or.inl hadj
          · exact Or.inr hadj
        have hmem := hc'L a ha'
        simp only [L', hab, if_true] at hmem
        simp only [c, ha12, if_false, hb12, if_true]
        exact (Finset.mem_erase.mp hmem).1
      · have ha' : a ∈ U' := Finset.mem_erase.mpr ⟨fun h => ha12 (Or.inr h), Finset.mem_erase.mpr ⟨fun h => ha12 (Or.inl h), ha⟩⟩
        have hb' : b ∈ U' := Finset.mem_erase.mpr ⟨fun h => hb12 (Or.inr h), Finset.mem_erase.mpr ⟨fun h => hb12 (Or.inl h), hb⟩⟩
        simp only [c, ha12, hb12, if_false]
        exact hc'adj a ha' b hb' hadj

end GraphHelpers

section TwoConnGallai

variable {V : Type*} [Fintype V]

lemma reachIn_ne_exists_adj {G : SimpleGraph V} {U : Finset V} {a b : V}
    (h : ReachIn G U a b) (hne : a ≠ b) : ∃ w ∈ U, G.Adj a w := by
  cases h using Relation.ReflTransGen.head_induction_on with
  | refl => exact (hne rfl).elim
  | head hstep _ => exact ⟨_, hstep.2.1, hstep.2.2⟩

lemma degIn_ge_two [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V}
    (hcard : 3 ≤ U.card) (h2conn : ∀ y ∈ U, ConnIn G (U.erase y))
    {v : V} (hv : v ∈ U) : 2 ≤ degIn G U v := by
  have h1 : ∃ y ∈ U, G.Adj v y := by
    have hpos : 2 ≤ (U.erase v).card := by rw [Finset.card_erase_of_mem hv]; omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < (U.erase v).card)
    have hne : u ≠ v := (Finset.mem_erase.mp hu).1
    have huU : u ∈ U := (Finset.mem_erase.mp hu).2
    have hpos2 : 1 ≤ ((U.erase v).erase u).card := by
      rw [Finset.card_erase_of_mem hu]; omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < ((U.erase v).erase u).card)
    have hzu : z ≠ u := (Finset.mem_erase.mp hz).1
    have hzv : z ≠ v := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1
    have hzU : z ∈ U := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2
    have hreach := h2conn u huU v (Finset.mem_erase.mpr ⟨hne.symm, hv⟩) z (Finset.mem_erase.mpr ⟨hzu, hzU⟩)
    obtain ⟨w, hw, hadj⟩ := reachIn_ne_exists_adj hreach hzv.symm
    exact ⟨w, (Finset.mem_erase.mp hw).2, hadj⟩
  obtain ⟨y, hyU, hvy⟩ := h1
  have hvy_ne : v ≠ y := G.ne_of_adj hvy
  have herase_card : 2 ≤ (U.erase y).card := by rw [Finset.card_erase_of_mem hyU]; omega
  have hv_er : v ∈ U.erase y := Finset.mem_erase.mpr ⟨hvy_ne, hv⟩
  have h2card : 1 ≤ ((U.erase y).erase v).card := by rw [Finset.card_erase_of_mem hv_er]; omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < ((U.erase y).erase v).card)
  have hzv : z ≠ v := (Finset.mem_erase.mp hz).1
  have hz_er : z ∈ U.erase y := (Finset.mem_erase.mp hz).2
  have hreach := h2conn y hyU v hv_er z hz_er
  obtain ⟨w, hw_er, hvw⟩ := reachIn_ne_exists_adj hreach hzv.symm
  have hwy : w ≠ y := (Finset.mem_erase.mp hw_er).1
  have hwU : w ∈ U := (Finset.mem_erase.mp hw_er).2
  have hsub : ({y, w} : Finset V) ⊆ U.filter (fun u => G.Adj v u) := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hyU, hvy⟩
    · exact Finset.mem_filter.mpr ⟨hwU, hvw⟩
  have hpair : ({y, w} : Finset V).card = 2 := Finset.card_pair hwy.symm
  calc 2 = ({y, w} : Finset V).card := hpair.symm
    _ ≤ (U.filter (fun u => G.Adj v u)).card := Finset.card_le_card hsub

lemma reachIn_exit_set {G : SimpleGraph V} {U S : Finset V} {a b : V}
    (hreach : ReachIn G U a b) (ha : a ∈ S) (hb : b ∉ S) :
    ∃ u ∈ S, ∃ v ∈ U, v ∉ S ∧ G.Adj u v := by
  classical
  induction hreach with
  | refl => exact (hb ha).elim
  | @tail c d hprev hstep ih =>
    by_cases hc : c ∈ S
    · exact ⟨c, hc, d, hstep.2.1, hb, hstep.2.2⟩
    · exact ih hc

def IsSep [DecidableEq V] (G : SimpleGraph V) (U' : Finset V) (y : V) (K : Finset V) : Prop :=
  y ∈ U' ∧ K.Nonempty ∧ K ⊆ U'.erase y ∧ (∃ w ∈ U'.erase y, w ∉ K) ∧
  ∀ a ∈ K, ∀ b ∈ U'.erase y, G.Adj a b → b ∈ K

lemma isSep_compl [DecidableEq V] {G : SimpleGraph V} {U' : Finset V} {y : V} {K : Finset V}
    (h : IsSep G U' y K) : IsSep G U' y ((U'.erase y) \ K) := by
  obtain ⟨hy, ⟨a, haK⟩, hKsub, ⟨w, hwU, hwK⟩, hclosed⟩ := h
  refine ⟨hy, ⟨w, Finset.mem_sdiff.mpr ⟨hwU, hwK⟩⟩, Finset.sdiff_subset,
    ⟨a, hKsub haK, fun hmem => (Finset.mem_sdiff.mp hmem).2 haK⟩, ?_⟩
  intro u hu v hv huv
  have huU := (Finset.mem_sdiff.mp hu).1
  have huK := (Finset.mem_sdiff.mp hu).2
  refine Finset.mem_sdiff.mpr ⟨hv, fun hvK => huK (hclosed v hvK u huU huv.symm)⟩

lemma reachIn_avoid_sep [DecidableEq V] {G : SimpleGraph V} {U' S : Finset V} {y : V} {K : Finset V}
    (hsep : IsSep G U' y K) (hSU : S ⊆ U') {a b : V}
    (hreach : ReachIn G S a b) (ha : a ∉ K) :
    (b ∉ K → ReachIn G (S \ K) a b) ∧ (b ∈ K → y ∈ S ∧ ReachIn G (S \ K) a y) := by
  induction hreach with
  | refl =>
    exact ⟨fun _ => Relation.ReflTransGen.refl, fun haK => (ha haK).elim⟩
  | @tail c d hprev hstep ih =>
    by_cases hcK : c ∈ K
    · obtain ⟨hyS, hray⟩ := ih.2 hcK
      refine ⟨fun hdK => ?_, fun _ => ⟨hyS, hray⟩⟩
      have hdy : d = y := by
        by_contra hne
        have hd_er : d ∈ U'.erase y := Finset.mem_erase.mpr ⟨hne, hSU hstep.2.1⟩
        exact hdK (hsep.2.2.2.2 c hcK d hd_er hstep.2.2)
      rw [hdy]
      exact hray
    · have hrac := ih.1 hcK
      refine ⟨fun hdK => ?_, fun hdK => ?_⟩
      · exact Relation.ReflTransGen.tail hrac
          ⟨Finset.mem_sdiff.mpr ⟨hstep.1, hcK⟩, Finset.mem_sdiff.mpr ⟨hstep.2.1, hdK⟩, hstep.2.2⟩
      · have hcy : c = y := by
          by_contra hne
          have hc_er : c ∈ U'.erase y := Finset.mem_erase.mpr ⟨hne, hSU hstep.1⟩
          exact hcK (hsep.2.2.2.2 d hdK c hc_er hstep.2.2.symm)
        rw [← hcy]
        exact ⟨hstep.1, hrac⟩

lemma isSep_not_conn [DecidableEq V] {G : SimpleGraph V} {U' : Finset V} {y : V} {K : Finset V}
    (hsep : IsSep G U' y K) : ¬ ConnIn G (U'.erase y) := by
  intro hconn
  obtain ⟨_, ⟨a, haK⟩, hKsub, ⟨w, hwU, hwK⟩, hclosed⟩ := hsep
  have hreach := hconn a (hKsub haK) w hwU
  obtain ⟨u, huK, v, hvU, hvK, huv⟩ := reachIn_exit_set hreach haK hwK
  exact hvK (hclosed u huK v hvU huv)

lemma exists_sep_of_not_conn [DecidableEq V] {G : SimpleGraph V} {U' : Finset V} {y : V}
    (hy : y ∈ U') (hnc : ¬ ConnIn G (U'.erase y)) :
    ∃ K : Finset V, IsSep G U' y K := by
  classical
  unfold ConnIn at hnc
  push Not at hnc
  obtain ⟨a, ha, b, hb, hnr⟩ := hnc
  let K := (U'.erase y).filter (fun v => ReachIn G (U'.erase y) a v)
  refine ⟨K, hy, ⟨a, Finset.mem_filter.mpr ⟨ha, Relation.ReflTransGen.refl⟩⟩,
    Finset.filter_subset _ _, ⟨b, hb, fun hbK => hnr (Finset.mem_filter.mp hbK).2⟩, ?_⟩
  intro u hu v hv huv
  have huU := (Finset.mem_filter.mp hu).1
  have hrau := (Finset.mem_filter.mp hu).2
  exact Finset.mem_filter.mpr ⟨hv, Relation.ReflTransGen.tail hrau ⟨huU, hv, huv⟩⟩

lemma minimal_sep_erase_conn [DecidableEq V] {G : SimpleGraph V} {U' : Finset V}
    (hconn : ConnIn G U') {y : V} {K : Finset V} (hsep : IsSep G U' y K)
    (hmin : ∀ y' K', IsSep G U' y' K' → K' ⊆ K → K.card ≤ K'.card)
    {u : V} (huK : u ∈ K) : ConnIn G (U'.erase u) := by
  classical
  have huU : u ∈ U' := (Finset.mem_erase.mp (hsep.2.2.1 huK)).2
  have huy : u ≠ y := (Finset.mem_erase.mp (hsep.2.2.1 huK)).1
  have hy_er : y ∈ U'.erase u := Finset.mem_erase.mpr ⟨huy.symm, hsep.1⟩
  have hout : ∀ v ∈ U', v ∉ K → ReachIn G (U'.erase u) v y := by
    intro v hvU hvK
    have hyK : y ∉ K := fun h => (Finset.mem_erase.mp (hsep.2.2.1 h)).1 rfl
    have hr := (reachIn_avoid_sep hsep (Finset.Subset.refl U') (hconn v hvU y hsep.1) hvK).1 hyK
    have hsub : U' \ K ⊆ U'.erase u := by
      intro z hz
      exact Finset.mem_erase.mpr ⟨fun hzu => (Finset.mem_sdiff.mp hz).2 (hzu ▸ huK),
        (Finset.mem_sdiff.mp hz).1⟩
    exact reachIn_mono hsub hr
  have hall : ∀ v ∈ U'.erase u, ReachIn G (U'.erase u) v y := by
    intro v hv
    by_cases hvK : v ∈ K
    · by_contra hnr
      let K' := (U'.erase u).filter (fun z => ReachIn G (U'.erase u) v z)
      have hK'_sub_K : K' ⊆ K := by
        intro z hz
        have hzU := (Finset.mem_erase.mp (Finset.mem_filter.mp hz).1).2
        have hrvz := (Finset.mem_filter.mp hz).2
        by_contra hzK
        exact hnr (hrvz.trans (hout z hzU hzK))
      have huK' : u ∉ K' := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
      have hK'_sep : IsSep G U' u K' := by
        refine ⟨huU, ⟨v, Finset.mem_filter.mpr ⟨hv, Relation.ReflTransGen.refl⟩⟩,
          Finset.filter_subset _ _,
          ⟨y, hy_er, fun hyK' => hnr (Finset.mem_filter.mp hyK').2⟩, ?_⟩
        intro a ha b hb hab
        exact Finset.mem_filter.mpr ⟨hb, Relation.ReflTransGen.tail (Finset.mem_filter.mp ha).2
          ⟨(Finset.mem_filter.mp ha).1, hb, hab⟩⟩
      have hlt : K'.card < K.card := Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.mpr ⟨hK'_sub_K, fun heq => huK' (heq ▸ huK)⟩)
      have hge := hmin u K' hK'_sep hK'_sub_K
      omega
    · exact hout v (Finset.mem_erase.mp hv).2 hvK
  intro a ha b hb
  exact (hall a ha).trans (reachIn_symm (hall b hb))

lemma exists_neighbor_in_sep [DecidableEq V] {G : SimpleGraph V} {U : Finset V} {x y : V} {K : Finset V}
    (hx : x ∈ U) (h2conn : ∀ z ∈ U, ConnIn G (U.erase z))
    (hsep : IsSep G (U.erase x) y K) : ∃ u ∈ K, G.Adj x u := by
  obtain ⟨hyU', ⟨a, haK⟩, hKsub, _, hclosed⟩ := hsep
  have hyU : y ∈ U := (Finset.mem_erase.mp hyU').2
  have hxy : x ≠ y := (Finset.mem_erase.mp hyU').1.symm
  have ha_er : a ∈ U.erase y := by
    have ha1 := hKsub haK
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ha1).1,
      (Finset.mem_erase.mp (Finset.mem_erase.mp ha1).2).2⟩
  have hx_er : x ∈ U.erase y := Finset.mem_erase.mpr ⟨hxy, hx⟩
  have hxK : x ∉ K := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp (hKsub h)).2).1 rfl
  have hreach := h2conn y hyU a ha_er x hx_er
  obtain ⟨u, huK, v, hv_er, hvK, huv⟩ := reachIn_exit_set hreach haK hxK
  have hvx : v = x := by
    by_contra hne
    have hv' : v ∈ (U.erase x).erase y := Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hv_er).1, Finset.mem_erase.mpr ⟨hne, (Finset.mem_erase.mp hv_er).2⟩⟩
    exact hvK (hclosed u huK v hv' huv)
  rw [hvx] at huv
  exact ⟨u, huK, huv.symm⟩

lemma degIn_all_two_of_no_cherry [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {L : V → Finset (Fin 3)}
    (colorable_of_cherry :
      ∀ {U : Finset V} {L : V → Finset (Fin 3)},
        ConnIn G U → (∀ v ∈ U, degIn G U v ≤ (L v).card) →
        ∀ {w u₁ u₂ : V}, w ∈ U → u₁ ∈ U → u₂ ∈ U →
        G.Adj w u₁ → G.Adj w u₂ → u₁ ≠ u₂ → ¬ G.Adj u₁ u₂ →
        2 ≤ degIn G U u₁ → 2 ≤ degIn G U u₂ →
        ConnIn G ((U.erase u₁).erase u₂) → Colorable G U L)
    (hconn : ConnIn G U) (hcard : 3 ≤ U.card)
    (hmax : ∀ v ∈ U, degIn G U v ≤ 3)
    (hnk4 : ¬ (U.card = 4 ∧ ∀ v ∈ U, degIn G U v = 3))
    (h2conn : ∀ y ∈ U, ConnIn G (U.erase y))
    (hdeg : ∀ v ∈ U, degIn G U v ≤ (L v).card)
    (hunc : ¬ Colorable G U L) :
    ∀ v ∈ U, degIn G U v = 2 := by
  classical
  have hge2 : ∀ v ∈ U, 2 ≤ degIn G U v := fun v hv => degIn_ge_two hcard h2conn hv
  intro v hv
  by_contra hne2
  have h3 : ∃ x ∈ U, degIn G U x = 3 := by
    have hle := hmax v hv
    have hge := hge2 v hv
    exact ⟨v, hv, by omega⟩
  obtain ⟨x, hxU, hdx⟩ := h3
  let U' := U.erase x
  have hconn' : ConnIn G U' := h2conn x hxU
  have hNsub_x : U.filter (fun w => G.Adj x w) ⊆ U' := by
    intro w hw
    exact Finset.mem_erase.mpr ⟨(G.ne_of_adj (Finset.mem_filter.mp hw).2).symm,
      (Finset.mem_filter.mp hw).1⟩
  have hU_ge4 : 4 ≤ U.card := by
    have hle := Finset.card_le_card hNsub_x
    have hce : U'.card = U.card - 1 := Finset.card_erase_of_mem hxU
    have hdx' : (U.filter (fun w => G.Adj x w)).card = 3 := hdx
    omega
  by_cases h2c' : ∀ y ∈ U', ConnIn G (U'.erase y)
  · by_cases hc4 : U.card = 4
    · have hnotall3 : ¬ ∀ w ∈ U, degIn G U w = 3 := fun hall => hnk4 ⟨hc4, hall⟩
      push Not at hnotall3
      obtain ⟨u₁, hu₁U, hdu₁_ne3⟩ := hnotall3
      have hdu₁ : degIn G U u₁ = 2 := by
        have := hmax u₁ hu₁U; have := hge2 u₁ hu₁U; omega
      have hu₁x : u₁ ≠ x := fun h => hdu₁_ne3 (h ▸ hdx)
      have hu₁U' : u₁ ∈ U' := Finset.mem_erase.mpr ⟨hu₁x, hu₁U⟩
      have hU'card : U'.card = 3 := by rw [Finset.card_erase_of_mem hxU]; omega
      have hNeq : U.filter (fun w => G.Adj x w) = U' :=
        Finset.eq_of_subset_of_card_le hNsub_x (by rw [hU'card]; exact le_of_eq hdx.symm)
      have hxadj : ∀ w ∈ U', G.Adj x w := fun w hw => (Finset.mem_filter.mp (hNeq.symm ▸ hw)).2
      have hN1sub : U.filter (fun w => G.Adj u₁ w) ⊆ U.erase u₁ := by
        intro w hw
        exact Finset.mem_erase.mpr ⟨(G.ne_of_adj (Finset.mem_filter.mp hw).2).symm,
          (Finset.mem_filter.mp hw).1⟩
      have hcard_er1 : (U.erase u₁).card = 3 := by rw [Finset.card_erase_of_mem hu₁U]; omega
      have hdiff : ((U.erase u₁) \ U.filter (fun w => G.Adj u₁ w)).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hN1sub, hcard_er1]
        change 0 < 3 - degIn G U u₁
        omega
      obtain ⟨u₂, hu₂mem⟩ := hdiff
      have hu₂_er1 := (Finset.mem_sdiff.mp hu₂mem).1
      have hu₂_nadj_mem := (Finset.mem_sdiff.mp hu₂mem).2
      have hu₂_ne1 : u₂ ≠ u₁ := (Finset.mem_erase.mp hu₂_er1).1
      have hu₂U : u₂ ∈ U := (Finset.mem_erase.mp hu₂_er1).2
      have hnadj : ¬ G.Adj u₁ u₂ := fun h => hu₂_nadj_mem (Finset.mem_filter.mpr ⟨hu₂U, h⟩)
      have hu₂x : u₂ ≠ x := fun h => hnadj (h ▸ (hxadj u₁ hu₁U').symm)
      have hu₂U' : u₂ ∈ U' := Finset.mem_erase.mpr ⟨hu₂x, hu₂U⟩
      have hconn_rem : ConnIn G ((U.erase u₁).erase u₂) := by
        have hx_rem : x ∈ (U.erase u₁).erase u₂ :=
          Finset.mem_erase.mpr ⟨hu₂x.symm, Finset.mem_erase.mpr ⟨hu₁x.symm, hxU⟩⟩
        have hto_x : ∀ w ∈ (U.erase u₁).erase u₂, ReachIn G ((U.erase u₁).erase u₂) w x := by
          intro w hw
          by_cases hwx : w = x
          · rw [hwx]; exact Relation.ReflTransGen.refl
          · have hwU' : w ∈ U' := Finset.mem_erase.mpr
              ⟨hwx, (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).2⟩
            exact Relation.ReflTransGen.single ⟨hw, hx_rem, (hxadj w hwU').symm⟩
        intro a ha b hb
        exact (hto_x a ha).trans (reachIn_symm (hto_x b hb))
      exact hunc (colorable_of_cherry hconn hdeg hxU hu₁U hu₂U
        (hxadj u₁ hu₁U') (hxadj u₂ hu₂U') hu₂_ne1.symm hnadj
        (hge2 u₁ hu₁U) (hge2 u₂ hu₂U) hconn_rem)
    · have hc5 : 5 ≤ U.card := by omega
      let N := U.filter (fun w => G.Adj x w)
      have hU'card : 4 ≤ U'.card := by rw [Finset.card_erase_of_mem hxU]; omega
      have hNcard : N.card = 3 := hdx
      have hNne : N.Nonempty := Finset.card_pos.mp (by omega)
      have houtne : (U' \ N).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hNsub_x]
        change 0 < U'.card - N.card
        omega
      obtain ⟨w₀, hw₀N⟩ := hNne
      obtain ⟨z₀, hz₀⟩ := houtne
      have hr := hconn' w₀ (hNsub_x hw₀N) z₀ (Finset.mem_sdiff.mp hz₀).1
      obtain ⟨w, hwN, z, hzU', hzN, hwz⟩ := reachIn_exit_set hr hw₀N (Finset.mem_sdiff.mp hz₀).2
      have hwU : w ∈ U := (Finset.mem_filter.mp hwN).1
      have hxw : G.Adj x w := (Finset.mem_filter.mp hwN).2
      have hzx : z ≠ x := (Finset.mem_erase.mp hzU').1
      have hzU : z ∈ U := (Finset.mem_erase.mp hzU').2
      have hnxz : ¬ G.Adj x z := fun h => hzN (Finset.mem_filter.mpr ⟨hzU, h⟩)
      exact hunc (colorable_of_cherry hconn hdeg hwU hxU hzU
        hxw.symm hwz hzx.symm hnxz (hge2 x hxU) (hge2 z hzU) (h2c' z hzU'))
  · push Not at h2c'
    obtain ⟨y₀, hy₀U', hnc₀⟩ := h2c'
    obtain ⟨K₀, hsep₀⟩ := exists_sep_of_not_conn hy₀U' hnc₀
    let P1 : Nat → Prop := fun m => ∃ y K, IsSep G U' y K ∧ K.card = m
    have hP1 : ∃ m, P1 m := ⟨K₀.card, y₀, K₀, hsep₀, rfl⟩
    let m₁ := Nat.find hP1
    obtain ⟨y₁, K₁, hsep₁, hcard₁⟩ := Nat.find_spec hP1
    have hmin₁ : ∀ y' K', IsSep G U' y' K' → K' ⊆ K₁ → K₁.card ≤ K'.card := by
      intro y' K' hsep' _
      rw [hcard₁]
      exact Nat.find_min' hP1 ⟨y', K', hsep', rfl⟩
    let R₁ := (U'.erase y₁) \ K₁
    have hsepR₁ : IsSep G U' y₁ R₁ := isSep_compl hsep₁
    let P2 : Nat → Prop := fun m => ∃ y K, IsSep G U' y K ∧ K ⊆ R₁ ∧ K.card = m
    have hP2 : ∃ m, P2 m := ⟨R₁.card, y₁, R₁, hsepR₁, Finset.Subset.refl R₁, rfl⟩
    let m₂ := Nat.find hP2
    obtain ⟨y₂, K₂, hsep₂, hK₂R₁, hcard₂⟩ := Nat.find_spec hP2
    have hmin₂ : ∀ y' K', IsSep G U' y' K' → K' ⊆ K₂ → K₂.card ≤ K'.card := by
      intro y' K' hsep' hsub
      rw [hcard₂]
      exact Nat.find_min' hP2 ⟨y', K', hsep', hsub.trans hK₂R₁, rfl⟩
    obtain ⟨u₁, hu₁K₁, hxu₁⟩ := exists_neighbor_in_sep hxU h2conn hsep₁
    obtain ⟨u₂, hu₂K₂, hxu₂⟩ := exists_neighbor_in_sep hxU h2conn hsep₂
    have hu₁U' : u₁ ∈ U' := (Finset.mem_erase.mp (hsep₁.2.2.1 hu₁K₁)).2
    have hu₂R₁ : u₂ ∈ R₁ := hK₂R₁ hu₂K₂
    have hu₂_ery₁ : u₂ ∈ U'.erase y₁ := (Finset.mem_sdiff.mp hu₂R₁).1
    have hu₂nK₁ : u₂ ∉ K₁ := (Finset.mem_sdiff.mp hu₂R₁).2
    have hu₂U' : u₂ ∈ U' := (Finset.mem_erase.mp hu₂_ery₁).2
    have hu₁U : u₁ ∈ U := (Finset.mem_erase.mp hu₁U').2
    have hu₂U : u₂ ∈ U := (Finset.mem_erase.mp hu₂U').2
    have hne12 : u₁ ≠ u₂ := fun h => hu₂nK₁ (h ▸ hu₁K₁)
    have hnadj12 : ¬ G.Adj u₁ u₂ := fun h => hu₂nK₁ (hsep₁.2.2.2.2 u₁ hu₁K₁ u₂ hu₂_ery₁ h)
    have hy₂nK₁ : y₂ ∉ K₁ := fun hy₂K₁ =>
      isSep_not_conn hsep₂ (minimal_sep_erase_conn hconn' hsep₁ hmin₁ hy₂K₁)
    have hy₁nK₂ : y₁ ∉ K₂ := fun hy₁K₂ =>
      (Finset.mem_erase.mp (Finset.mem_sdiff.mp (hK₂R₁ hy₁K₂)).1).1 rfl
    have hy₁nK₁ : y₁ ∉ K₁ := fun h => (Finset.mem_erase.mp (hsep₁.2.2.1 h)).1 rfl
    have hy₂nK₂ : y₂ ∉ K₂ := fun h => (Finset.mem_erase.mp (hsep₂.2.2.1 h)).1 rfl
    have hK₁K₂_disj : ∀ z, z ∈ K₁ → z ∉ K₂ := fun z hz1 hz2 =>
      (Finset.mem_sdiff.mp (hK₂R₁ hz2)).2 hz1
    let W := (U.erase u₁).erase u₂
    have hsub_W : ∀ S : Finset V, S ⊆ U' → u₁ ∉ S → u₂ ∉ S → S ⊆ W := by
      intro S hSU' h1 h2 z hz
      exact Finset.mem_erase.mpr ⟨fun h => h2 (h ▸ hz),
        Finset.mem_erase.mpr ⟨fun h => h1 (h ▸ hz), (Finset.mem_erase.mp (hSU' hz)).2⟩⟩
    have hy₂_to_y₁ : ReachIn G W y₂ y₁ := by
      have hr1 := (reachIn_avoid_sep hsep₁ (Finset.Subset.refl U')
        (hconn' y₂ hsep₂.1 y₁ hsep₁.1) hy₂nK₁).1 hy₁nK₁
      have hr2 := (reachIn_avoid_sep hsep₂ Finset.sdiff_subset hr1 hy₂nK₂).1 hy₁nK₂
      have hsub : (U' \ K₁) \ K₂ ⊆ W := hsub_W _ (Finset.sdiff_subset.trans Finset.sdiff_subset)
        (fun h => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h).1).2 hu₁K₁)
        (fun h => (Finset.mem_sdiff.mp h).2 hu₂K₂)
      exact reachIn_mono hsub hr2
    have hU'_to_y₁ : ∀ w ∈ U', w ≠ u₁ → w ≠ u₂ → ReachIn G W w y₁ := by
      intro w hwU' hw1 hw2
      by_cases hwK₁ : w ∈ K₁
      · have hc1 := minimal_sep_erase_conn hconn' hsep₁ hmin₁ hu₁K₁
        have hwnK₂ : w ∉ K₂ := hK₁K₂_disj w hwK₁
        have hr := (reachIn_avoid_sep hsep₂ (Finset.erase_subset u₁ U')
          (hc1 w (Finset.mem_erase.mpr ⟨hw1, hwU'⟩)
            y₁ (Finset.mem_erase.mpr ⟨fun h => hy₁nK₁ (h ▸ hu₁K₁), hsep₁.1⟩)) hwnK₂).1 hy₁nK₂
        have hsub : (U'.erase u₁) \ K₂ ⊆ W := hsub_W _
          (Finset.sdiff_subset.trans (Finset.erase_subset u₁ U'))
          (fun h => (Finset.mem_erase.mp (Finset.mem_sdiff.mp h).1).1 rfl)
          (fun h => (Finset.mem_sdiff.mp h).2 hu₂K₂)
        exact reachIn_mono hsub hr
      · by_cases hwK₂ : w ∈ K₂
        · have hc2 := minimal_sep_erase_conn hconn' hsep₂ hmin₂ hu₂K₂
          have hr := (reachIn_avoid_sep hsep₁ (Finset.erase_subset u₂ U')
            (hc2 w (Finset.mem_erase.mpr ⟨hw2, hwU'⟩)
              y₂ (Finset.mem_erase.mpr ⟨fun h => hy₂nK₂ (h ▸ hu₂K₂), hsep₂.1⟩)) hwK₁).1 hy₂nK₁
          have hsub : (U'.erase u₂) \ K₁ ⊆ W := hsub_W _
            (Finset.sdiff_subset.trans (Finset.erase_subset u₂ U'))
            (fun h => (Finset.mem_sdiff.mp h).2 hu₁K₁)
            (fun h => (Finset.mem_erase.mp (Finset.mem_sdiff.mp h).1).1 rfl)
          exact (reachIn_mono hsub hr).trans hy₂_to_y₁
        · have hr1 := (reachIn_avoid_sep hsep₁ (Finset.Subset.refl U')
            (hconn' w hwU' y₁ hsep₁.1) hwK₁).1 hy₁nK₁
          have hr2 := (reachIn_avoid_sep hsep₂ Finset.sdiff_subset hr1 hwK₂).1 hy₁nK₂
          have hsub : (U' \ K₁) \ K₂ ⊆ W := hsub_W _ (Finset.sdiff_subset.trans Finset.sdiff_subset)
            (fun h => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h).1).2 hu₁K₁)
            (fun h => (Finset.mem_sdiff.mp h).2 hu₂K₂)
          exact reachIn_mono hsub hr2
    have hxW : x ∈ W := Finset.mem_erase.mpr
      ⟨(G.ne_of_adj hxu₂), Finset.mem_erase.mpr ⟨(G.ne_of_adj hxu₁), hxU⟩⟩
    have hx_to_y₁ : ReachIn G W x y₁ := by
      have hcard_nb : ((U.filter (fun w => G.Adj x w)) \ {u₁, u₂}).Nonempty := by
        apply Finset.card_pos.mp
        have hsub12 : ({u₁, u₂} : Finset V) ⊆ U.filter (fun w => G.Adj x w) := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hu₁U, hxu₁⟩
          · exact Finset.mem_filter.mpr ⟨hu₂U, hxu₂⟩
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub12, Finset.card_pair hne12]
        change 0 < degIn G U x - 2
        omega
      obtain ⟨u₃, hu₃mem⟩ := hcard_nb
      have hu₃f := (Finset.mem_sdiff.mp hu₃mem).1
      have hu₃not := (Finset.mem_sdiff.mp hu₃mem).2
      have hu₃U := (Finset.mem_filter.mp hu₃f).1
      have hxu₃ := (Finset.mem_filter.mp hu₃f).2
      have hu₃1 : u₃ ≠ u₁ := fun h => hu₃not (by simp [h])
      have hu₃2 : u₃ ≠ u₂ := fun h => hu₃not (by simp [h])
      have hu₃x : u₃ ≠ x := (G.ne_of_adj hxu₃).symm
      have hu₃W : u₃ ∈ W := Finset.mem_erase.mpr ⟨hu₃2, Finset.mem_erase.mpr ⟨hu₃1, hu₃U⟩⟩
      exact Relation.ReflTransGen.head ⟨hxW, hu₃W, hxu₃⟩
        (hU'_to_y₁ u₃ (Finset.mem_erase.mpr ⟨hu₃x, hu₃U⟩) hu₃1 hu₃2)
    have hconnW : ConnIn G W := by
      have hallW : ∀ w ∈ W, ReachIn G W w y₁ := by
        intro w hwW
        have hw2 : w ≠ u₂ := (Finset.mem_erase.mp hwW).1
        have hw1 : w ≠ u₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hwW).2).1
        have hwU : w ∈ U := (Finset.mem_erase.mp (Finset.mem_erase.mp hwW).2).2
        by_cases hwx : w = x
        · exact hwx ▸ hx_to_y₁
        · exact hU'_to_y₁ w (Finset.mem_erase.mpr ⟨hwx, hwU⟩) hw1 hw2
      intro a ha b hb
      exact (hallW a ha).trans (reachIn_symm (hallW b hb))
    exact hunc (colorable_of_cherry hconn hdeg hxU hu₁U hu₂U
      hxu₁ hxu₂ hne12 hnadj12 (hge2 u₁ hu₁U) (hge2 u₂ hu₂U) hconnW)

lemma two_regular_other_neighbor [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V}
    (hreg : ∀ v ∈ U, degIn G U v = 2) {u v : V} (hu : u ∈ U) (hv : v ∈ U) (huv : G.Adj u v) :
    ∃ w ∈ U, G.Adj v w ∧ w ≠ u ∧ ∀ z ∈ U, G.Adj v z → z = u ∨ z = w := by
  have hcard : (U.filter (fun z => G.Adj v z)).card = 2 := hreg v hv
  have hu_mem : u ∈ U.filter (fun z => G.Adj v z) := Finset.mem_filter.mpr ⟨hu, huv.symm⟩
  have h1 : ((U.filter (fun z => G.Adj v z)).erase u).card = 1 := by
    rw [Finset.card_erase_of_mem hu_mem, hcard]
  obtain ⟨w, hw_eq⟩ := Finset.card_eq_one.mp h1
  have hw_mem : w ∈ (U.filter (fun z => G.Adj v z)).erase u := by rw [hw_eq]; simp
  have hwu : w ≠ u := (Finset.mem_erase.mp hw_mem).1
  have hwU : w ∈ U := (Finset.mem_filter.mp (Finset.mem_erase.mp hw_mem).2).1
  have hvw : G.Adj v w := (Finset.mem_filter.mp (Finset.mem_erase.mp hw_mem).2).2
  refine ⟨w, hwU, hvw, hwu, ?_⟩
  intro z hzU hvz
  by_cases hzu : z = u
  · exact Or.inl hzu
  · right
    have hz_er : z ∈ (U.filter (fun t => G.Adj v t)).erase u :=
      Finset.mem_erase.mpr ⟨hzu, Finset.mem_filter.mpr ⟨hzU, hvz⟩⟩
    rw [hw_eq, Finset.mem_singleton] at hz_er
    exact hz_er

lemma two_regular_even_two_colorable [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} (hconn : ConnIn G U) (hcard : 3 ≤ U.card)
    (hreg : ∀ v ∈ U, degIn G U v = 2) (heven : Even U.card)
    {c₀ c₁ : Fin 3} (hcne : c₀ ≠ c₁) :
    ∃ c : V → Fin 3, (∀ v ∈ U, c v = c₀ ∨ c v = c₁) ∧
      ∀ u ∈ U, ∀ v ∈ U, G.Adj u v → c u ≠ c v := by
  classical
  obtain ⟨v₀, hv₀U⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
  have hv₀deg : (U.filter (fun z => G.Adj v₀ z)).card = 2 := hreg v₀ hv₀U
  obtain ⟨v₁, hv₁mem⟩ := Finset.card_pos.mp (by omega : 0 < (U.filter (fun z => G.Adj v₀ z)).card)
  have hv₁U : v₁ ∈ U := (Finset.mem_filter.mp hv₁mem).1
  have hv₀₁ : G.Adj v₀ v₁ := (Finset.mem_filter.mp hv₁mem).2
  let step : V × V → V × V := fun p =>
    if h : p.1 ∈ U ∧ p.2 ∈ U ∧ G.Adj p.1 p.2 then
      (p.2, Classical.choose (two_regular_other_neighbor hreg h.1 h.2.1 h.2.2))
    else p
  let walk : Nat → V × V := Nat.rec (v₀, v₁) (fun _ p => step p)
  have hwalk_ok : ∀ k, (walk k).1 ∈ U ∧ (walk k).2 ∈ U ∧ G.Adj (walk k).1 (walk k).2 := by
    intro k
    induction k with
    | zero => exact ⟨hv₀U, hv₁U, hv₀₁⟩
    | succ k ih =>
      show (step (walk k)).1 ∈ U ∧ (step (walk k)).2 ∈ U ∧ G.Adj (step (walk k)).1 (step (walk k)).2
      simp only [step, dite_eq_left ih]
      have hspec := Classical.choose_spec (two_regular_other_neighbor hreg ih.1 ih.2.1 ih.2.2)
      exact ⟨ih.2.1, hspec.1, hspec.2.1⟩
  let seq : Nat → V := fun k => (walk k).1
  have hseq_mem : ∀ k, seq k ∈ U := fun k => (hwalk_ok k).1
  have hwalk_snd : ∀ k, (walk k).2 = seq (k + 1) := by
    intro k
    have ih := hwalk_ok k
    show (walk k).2 = (step (walk k)).1
    simp only [step, dite_eq_left ih]
  have hseq_adj : ∀ k, G.Adj (seq k) (seq (k + 1)) := by
    intro k
    rw [← hwalk_snd k]
    exact (hwalk_ok k).2.2
  have hseq_ne2 : ∀ k, seq (k + 2) ≠ seq k := by
    intro k
    have ih := hwalk_ok k
    have h1 : seq (k + 2) = (step (walk k)).2 := by
      rw [← hwalk_snd (k + 1)]
    rw [h1]
    simp only [step, dite_eq_left ih]
    exact (Classical.choose_spec (two_regular_other_neighbor hreg ih.1 ih.2.1 ih.2.2)).2.2.1
  have hseq_nb : ∀ k z, z ∈ U → G.Adj (seq (k + 1)) z → z = seq k ∨ z = seq (k + 2) := by
    intro k z hzU hadj
    have ih := hwalk_ok k
    have hspec := Classical.choose_spec (two_regular_other_neighbor hreg ih.1 ih.2.1 ih.2.2)
    have h1 : seq (k + 2) = Classical.choose (two_regular_other_neighbor hreg ih.1 ih.2.1 ih.2.2) := by
      rw [← hwalk_snd (k + 1)]
      show (step (walk k)).2 = _
      simp only [step, dite_eq_left ih]
    rw [h1]
    have hmid : (walk k).2 = seq (k + 1) := hwalk_snd k
    rw [← hmid] at hadj
    exact hspec.2.2.2 z hzU hadj
  have hrep : ∃ k > 0, ∃ i < k, seq i = seq k := by
    by_contra hnorep
    push Not at hnorep
    have hinj : Set.InjOn seq (Finset.range (U.card + 1)) := by
      intro a ha b hb hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hnorep b (by omega) a hlt hab
      · exact hnorep a (by omega) b hgt hab.symm
    have hsub : (Finset.range (U.card + 1)).image seq ⊆ U := by
      intro z hz
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hz
      exact hseq_mem k
    have hle := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hle
    omega
  let p := Nat.find hrep
  have hp_spec := Nat.find_spec hrep
  have hp_pos : 0 < p := hp_spec.1
  obtain ⟨i₀, hi₀lt, hseq_eq_raw⟩ := hp_spec.2
  have hseq_eq : seq i₀ = seq p := hseq_eq_raw
  have hinj_p : ∀ a < p, ∀ b < p, seq a = seq b → a = b := by
    intro a ha b hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Nat.find_min hrep hb ⟨by omega, a, hlt, hab⟩
    · exact Nat.find_min hrep ha ⟨by omega, b, hgt, hab.symm⟩
  have hi₀_zero : i₀ = 0 := by
    by_contra hne0
    have hi₀_pos : 0 < i₀ := Nat.pos_of_ne_zero hne0
    have hadj : G.Adj (seq i₀) (seq (p - 1)) := by
      rw [hseq_eq]
      have hsub1 : p - 1 + 1 = p := Nat.sub_add_cancel hp_pos
      have htmp := hseq_adj (p - 1)
      rw [hsub1] at htmp
      exact htmp.symm
    have hi₀_eq : i₀ - 1 + 1 = i₀ := Nat.sub_add_cancel hi₀_pos
    have hnb := hseq_nb (i₀ - 1) (seq (p - 1)) (hseq_mem (p - 1)) (by rwa [hi₀_eq])
    rcases hnb with h1 | h2
    · have hp1 : p - 1 < p := by omega
      exact (by omega : i₀ - 1 ≠ p - 1) (hinj_p (i₀ - 1) (by omega) (p - 1) hp1 h1.symm)
    · have hi1 : i₀ - 1 + 2 = i₀ + 1 := by omega
      rw [hi1] at h2
      by_cases hlt : i₀ + 1 < p - 1
      · exact (by omega : i₀ + 1 ≠ p - 1) (hinj_p (i₀ + 1) (by omega) (p - 1) (by omega) h2.symm)
      · by_cases heq1 : i₀ + 1 = p - 1
        · have hp2 : p = i₀ + 2 := by omega
          have htmp : seq i₀ = seq (i₀ + 2) := hp2 ▸ hseq_eq
          exact hseq_ne2 i₀ htmp.symm
        · have hi_last : i₀ = p - 1 := by omega
          rw [hi_last] at hadj
          exact G.ne_of_adj hadj rfl
  rw [hi₀_zero] at hseq_eq
  have hp3 : 3 ≤ p := by
    by_contra hlt3
    have h12 : p = 1 ∨ p = 2 := by omega
    rcases h12 with hp1 | hp2
    · have ha := hseq_adj 0
      have htmp : seq 0 = seq 1 := hp1 ▸ hseq_eq
      exact G.ne_of_adj ha htmp
    · have htmp : seq 0 = seq 2 := hp2 ▸ hseq_eq
      exact hseq_ne2 0 htmp.symm
  let S := (Finset.range p).image seq
  have hSsub : S ⊆ U := by
    intro z hz
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hz
    exact hseq_mem k
  have hSclosed : ∀ a ∈ S, ∀ b ∈ U, G.Adj a b → b ∈ S := by
    intro a haS b hbU hab
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp haS
    rw [Finset.mem_range] at hk
    by_cases hk0 : k = 0
    · subst hk0
      have hnb0_1 : seq 1 ∈ U.filter (fun z => G.Adj (seq 0) z) :=
        Finset.mem_filter.mpr ⟨hseq_mem 1, hseq_adj 0⟩
      have hadj_last : G.Adj (seq 0) (seq (p - 1)) := by
        rw [hseq_eq]
        have hsub1 : p - 1 + 1 = p := Nat.sub_add_cancel hp_pos
        have htmp := hseq_adj (p - 1)
        rw [hsub1] at htmp
        exact htmp.symm
      have hnb0_2 : seq (p - 1) ∈ U.filter (fun z => G.Adj (seq 0) z) :=
        Finset.mem_filter.mpr ⟨hseq_mem (p - 1), hadj_last⟩
      have hne_1p : seq 1 ≠ seq (p - 1) := fun h =>
        (by omega : 1 ≠ p - 1) (hinj_p 1 (by omega) (p - 1) (by omega) h)
      have hpair_sub : ({seq 1, seq (p - 1)} : Finset V) ⊆ U.filter (fun z => G.Adj (seq 0) z) := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hnb0_1
        · exact hnb0_2
      have hpair_eq : ({seq 1, seq (p - 1)} : Finset V) = U.filter (fun z => G.Adj (seq 0) z) :=
        Finset.eq_of_subset_of_card_le hpair_sub
          (by rw [Finset.card_pair hne_1p]; exact le_of_eq (hreg (seq 0) (hseq_mem 0)))
      have hb_pair : b ∈ ({seq 1, seq (p - 1)} : Finset V) := by
        rw [hpair_eq]
        exact Finset.mem_filter.mpr ⟨hbU, hab⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb_pair
      rcases hb_pair with rfl | rfl
      · exact Finset.mem_image.mpr ⟨1, Finset.mem_range.mpr (by omega), rfl⟩
      · exact Finset.mem_image.mpr ⟨p - 1, Finset.mem_range.mpr (by omega), rfl⟩
    · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
      have hk_eq : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
      have hnb := hseq_nb (k - 1) b hbU (by rwa [hk_eq])
      rcases hnb with rfl | rfl
      · exact Finset.mem_image.mpr ⟨k - 1, Finset.mem_range.mpr (by omega), rfl⟩
      · have hk2 : k - 1 + 2 = k + 1 := by omega
        rw [hk2]
        by_cases hkp : k + 1 = p
        · rw [hkp, ← hseq_eq]
          exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hp_pos, rfl⟩
        · exact Finset.mem_image.mpr ⟨k + 1, Finset.mem_range.mpr (by omega), rfl⟩
  have hSeqU : S = U := by
    apply Finset.Subset.antisymm hSsub
    intro w hwU
    by_contra hwS
    have h0S : seq 0 ∈ S := Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hp_pos, rfl⟩
    have hr := hconn (seq 0) (hseq_mem 0) w hwU
    obtain ⟨u, huS, v, hvU, hvS, huv⟩ := reachIn_exit_set hr h0S hwS
    exact hvS (hSclosed u huS v hvU huv)
  have hp_card : p = U.card := by
    have h1 : S.card = p := by
      rw [Finset.card_image_of_injOn (fun a ha b hb hab =>
        hinj_p a (Finset.mem_range.mp ha) b (Finset.mem_range.mp hb) hab), Finset.card_range]
    rw [← h1, hSeqU]
  have hp_even : Even p := hp_card ▸ heven
  let c : V → Fin 3 := fun v =>
    if h : ∃ k < p, seq k = v then
      if Nat.find h % 2 = 0 then c₀ else c₁
    else c₀
  have hc_seq : ∀ k < p, c (seq k) = if k % 2 = 0 then c₀ else c₁ := by
    intro k hk
    have hex : ∃ m < p, seq m = seq k := ⟨k, hk, rfl⟩
    have hfeq : Nat.find hex = k :=
      hinj_p (Nat.find hex) (Nat.find_spec hex).1 k hk (Nat.find_spec hex).2
    simp only [c, dite_eq_left hex, hfeq]
  refine ⟨c, ?_, ?_⟩
  · intro v hvU
    have hvS : v ∈ S := hSeqU.symm ▸ hvU
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hvS
    rw [hc_seq k (Finset.mem_range.mp hk)]
    by_cases hmod : k % 2 = 0
    · simp [hmod]
    · simp [hmod]
  · intro u huU v hvU huv
    have huS : u ∈ S := hSeqU.symm ▸ huU
    have hvS : v ∈ S := hSeqU.symm ▸ hvU
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp huS
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hvS
    rw [Finset.mem_range] at hi hj
    rw [hc_seq i hi, hc_seq j hj]
    obtain ⟨m, hm⟩ := hp_even
    have hpar : i % 2 ≠ j % 2 := by
      by_cases hi0 : i = 0
      · subst hi0
        have hadj_last : G.Adj (seq 0) (seq (p - 1)) := by
          rw [hseq_eq]
          have hsub1 : p - 1 + 1 = p := Nat.sub_add_cancel hp_pos
          have htmp := hseq_adj (p - 1)
          rw [hsub1] at htmp
          exact htmp.symm
        have hne_1p : seq 1 ≠ seq (p - 1) := fun h =>
          (by omega : 1 ≠ p - 1) (hinj_p 1 (by omega) (p - 1) (by omega) h)
        have hpair_sub : ({seq 1, seq (p - 1)} : Finset V) ⊆ U.filter (fun z => G.Adj (seq 0) z) := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hseq_mem 1, hseq_adj 0⟩
          · exact Finset.mem_filter.mpr ⟨hseq_mem (p - 1), hadj_last⟩
        have hpair_eq : ({seq 1, seq (p - 1)} : Finset V) = U.filter (fun z => G.Adj (seq 0) z) :=
          Finset.eq_of_subset_of_card_le hpair_sub
            (by rw [Finset.card_pair hne_1p]; exact le_of_eq (hreg (seq 0) (hseq_mem 0)))
        have hj_mem : seq j ∈ ({seq 1, seq (p - 1)} : Finset V) := by
          rw [hpair_eq]
          exact Finset.mem_filter.mpr ⟨hseq_mem j, huv⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj_mem
        rcases hj_mem with h1 | h2
        · have hj1 : j = 1 := hinj_p j hj 1 (by omega) h1
          omega
        · have hjp : j = p - 1 := hinj_p j hj (p - 1) (by omega) h2
          omega
      · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
        have hi_eq : i - 1 + 1 = i := Nat.sub_add_cancel hi_pos
        have hnb := hseq_nb (i - 1) (seq j) (hseq_mem j) (by rwa [hi_eq])
        rcases hnb with h1 | h2
        · have hj1 : j = i - 1 := hinj_p j hj (i - 1) (by omega) h1
          omega
        · have hi2 : i - 1 + 2 = i + 1 := by omega
          rw [hi2] at h2
          by_cases hip : i + 1 = p
          · rw [hip, ← hseq_eq] at h2
            have hj0 : j = 0 := hinj_p j hj 0 hp_pos h2
            omega
          · have hj2 : j = i + 1 := hinj_p j hj (i + 1) (by omega) h2
            omega
    by_cases h1 : i % 2 = 0
    · have h2 : j % 2 ≠ 0 := fun h => hpar (h1.trans h.symm)
      simp [h1, h2, hcne]
    · have h2 : j % 2 = 0 := by omega
      simp [h1, h2, hcne.symm]

theorem two_conn_gallai_aux [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (colorable_of_strict_slack :
      ∀ {U : Finset V} {L : V → Finset (Fin 3)},
        (∀ v ∈ U, degIn G U v ≤ (L v).card) →
        (∀ u ∈ U, ∃ r ∈ U, ReachIn G U u r ∧ degIn G U r < (L r).card) →
        Colorable G U L)
    (colorable_of_cherry :
      ∀ {U : Finset V} {L : V → Finset (Fin 3)},
        ConnIn G U → (∀ v ∈ U, degIn G U v ≤ (L v).card) →
        ∀ {w u₁ u₂ : V}, w ∈ U → u₁ ∈ U → u₂ ∈ U →
        G.Adj w u₁ → G.Adj w u₂ → u₁ ≠ u₂ → ¬ G.Adj u₁ u₂ →
        2 ≤ degIn G U u₁ → 2 ≤ degIn G U u₂ →
        ConnIn G ((U.erase u₁).erase u₂) → Colorable G U L)
    {U : Finset V} {L : V → Finset (Fin 3)}
    (hconn : ConnIn G U) (hcard : 3 ≤ U.card)
    (hmax : ∀ v ∈ U, degIn G U v ≤ 3)
    (hnk4 : ¬ (U.card = 4 ∧ ∀ v ∈ U, degIn G U v = 3))
    (h2conn : ∀ y ∈ U, ConnIn G (U.erase y))
    (hdeg : ∀ v ∈ U, degIn G U v ≤ (L v).card)
    (hunc : ¬ Colorable G U L) :
    (∀ v ∈ U, degIn G U v = 2) ∧ Odd U.card := by
  classical
  have hreg : ∀ v ∈ U, degIn G U v = 2 :=
    degIn_all_two_of_no_cherry colorable_of_cherry hconn hcard hmax hnk4 h2conn hdeg hunc
  refine ⟨hreg, ?_⟩
  by_contra hnodd
  have heven : Even U.card := Nat.not_odd_iff_even.mp hnodd
  have hLcard : ∀ v ∈ U, (L v).card = 2 := by
    intro v hv
    by_contra hne2
    have hlt : degIn G U v < (L v).card := by
      have h1 := hdeg v hv
      have h2 := hreg v hv
      omega
    exact hunc (colorable_of_strict_slack hdeg (fun u hu => ⟨v, hv, hconn u hu v hv, hlt⟩))
  by_cases hconst : ∀ u ∈ U, ∀ v ∈ U, L u = L v
  · obtain ⟨v₀, hv₀U⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
    have h2c : (L v₀).card = 2 := hLcard v₀ hv₀U
    obtain ⟨c₀, c₁, hcne, hLeq⟩ := Finset.card_eq_two.mp h2c
    obtain ⟨c, hcin, hcadj⟩ := two_regular_even_two_colorable hconn hcard hreg heven hcne
    refine hunc ⟨c, ?_, hcadj⟩
    intro v hv
    rw [hconst v hv v₀ hv₀U, hLeq]
    rcases hcin v hv with h | h <;> simp [h]
  · push Not at hconst
    obtain ⟨u₀, hu₀U, v₀, hv₀U, hLne⟩ := hconst
    let S := U.filter (fun w => L w = L u₀)
    have hu₀S : u₀ ∈ S := Finset.mem_filter.mpr ⟨hu₀U, rfl⟩
    have hv₀nS : v₀ ∉ S := fun h => hLne (Finset.mem_filter.mp h).2.symm
    obtain ⟨a, haS, b, hbU, hbnS, hab⟩ := reachIn_exit_set (hconn u₀ hu₀U v₀ hv₀U) hu₀S hv₀nS
    have haU : a ∈ U := (Finset.mem_filter.mp haS).1
    have hLab : L a ≠ L b := fun heq => hbnS (Finset.mem_filter.mpr ⟨hbU, heq.symm.trans (Finset.mem_filter.mp haS).2⟩)
    have hcol_ex : ∃ col ∈ L a, col ∉ L b := by
      by_contra hall
      push Not at hall
      have hsub : L a ⊆ L b := fun z hz => hall z hz
      exact hLab (Finset.eq_of_subset_of_card_le hsub (by rw [hLcard a haU, hLcard b hbU]))
    obtain ⟨col, hcol_a, hcol_nb⟩ := hcol_ex
    let L' : V → Finset (Fin 3) := fun v => if G.Adj a v then (L v).erase col else L v
    have hdeg' : ∀ v ∈ U.erase a, degIn G (U.erase a) v ≤ (L' v).card := by
      intro v hv
      have hvU : v ∈ U := (Finset.mem_erase.mp hv).2
      have hL2 : (L v).card = 2 := hLcard v hvU
      have hd2 : (U.filter (fun w => G.Adj v w)).card = 2 := hreg v hvU
      by_cases hav : G.Adj a v
      · have ha_nb : a ∈ U.filter (fun w => G.Adj v w) := Finset.mem_filter.mpr ⟨haU, hav.symm⟩
        have hfeq : (U.erase a).filter (fun w => G.Adj v w) = (U.filter (fun w => G.Adj v w)).erase a := by
          ext w; simp only [Finset.mem_filter, Finset.mem_erase]; tauto
        have hd1 : degIn G (U.erase a) v = 1 := by
          unfold degIn; rw [hfeq, Finset.card_erase_of_mem ha_nb, hd2]
        simp only [L', ite_eq_left hav, hd1]
        have hce := Finset.pred_card_le_card_erase (s := L v) (a := col)
        omega
      · have hfeq : (U.erase a).filter (fun w => G.Adj v w) = U.filter (fun w => G.Adj v w) := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro ⟨⟨_, hwU⟩, hvw⟩; exact ⟨hwU, hvw⟩
          · rintro ⟨hwU, hvw⟩; exact ⟨⟨fun hwa => hav (hwa ▸ hvw.symm), hwU⟩, hvw⟩
        have hd2' : degIn G (U.erase a) v = 2 := by unfold degIn; rw [hfeq, hd2]
        simp only [L', ite_eq_right hav, hd2', hL2, le_refl]
    have hb_er : b ∈ U.erase a := Finset.mem_erase.mpr ⟨(G.ne_of_adj hab).symm, hbU⟩
    have hsl_b : degIn G (U.erase a) b < (L' b).card := by
      have ha_nb : a ∈ U.filter (fun w => G.Adj b w) := Finset.mem_filter.mpr ⟨haU, hab.symm⟩
      have hfeq : (U.erase a).filter (fun w => G.Adj b w) = (U.filter (fun w => G.Adj b w)).erase a := by
        ext w; simp only [Finset.mem_filter, Finset.mem_erase]; tauto
      have hd2b : (U.filter (fun w => G.Adj b w)).card = 2 := hreg b hbU
      have hd1 : degIn G (U.erase a) b = 1 := by
        unfold degIn; rw [hfeq, Finset.card_erase_of_mem ha_nb, hd2b]
      simp only [L', ite_eq_left hab, Finset.erase_eq_of_notMem hcol_nb, hLcard b hbU, hd1]
      omega
    obtain ⟨c, hcin, hcadj⟩ := colorable_of_strict_slack hdeg'
      (fun u hu => ⟨b, hb_er, h2conn a haU u hu b hb_er, hsl_b⟩)
    let c' : V → Fin 3 := Function.update c a col
    refine hunc ⟨c', ?_, ?_⟩
    · intro v hvU
      by_cases hva : v = a
      · subst hva; simp [c', hcol_a]
      · simp only [c', Function.update_of_ne hva]
        have hv_er : v ∈ U.erase a := Finset.mem_erase.mpr ⟨hva, hvU⟩
        have hmem := hcin v hv_er
        simp only [L'] at hmem
        by_cases hav : G.Adj a v
        · rw [ite_eq_left hav] at hmem; exact Finset.mem_of_mem_erase hmem
        · rw [ite_eq_right hav] at hmem; exact hmem
    · intro u huU v hvU huv
      by_cases hua : u = a
      · subst hua
        have hva : v ≠ u := (G.ne_of_adj huv).symm
        simp only [c', Function.update_self, Function.update_of_ne hva]
        have hmem := hcin v (Finset.mem_erase.mpr ⟨hva, hvU⟩)
        simp only [L', ite_eq_left huv] at hmem
        exact (Finset.mem_erase.mp hmem).1.symm
      · by_cases hva : v = a
        · subst hva
          simp only [c', Function.update_self, Function.update_of_ne hua]
          have hmem := hcin u (Finset.mem_erase.mpr ⟨hua, huU⟩)
          simp only [L', ite_eq_left huv.symm] at hmem
          exact (Finset.mem_erase.mp hmem).1
        · simp only [c', Function.update_of_ne hua, Function.update_of_ne hva]
          exact hcadj u (Finset.mem_erase.mpr ⟨hua, huU⟩) v (Finset.mem_erase.mpr ⟨hva, hvU⟩) huv

end TwoConnGallai

section GraphHelpers2

variable {V : Type*} [DecidableEq V] [Fintype V]

theorem two_conn_gallai {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {L : V → Finset (Fin 3)}
    (hconn : ConnIn G U) (hcard : 3 ≤ U.card)
    (hmax : ∀ v ∈ U, degIn G U v ≤ 3)
    (hnk4 : ¬ (U.card = 4 ∧ ∀ v ∈ U, degIn G U v = 3))
    (h2conn : ∀ y ∈ U, ConnIn G (U.erase y))
    (hdeg : ∀ v ∈ U, degIn G U v ≤ (L v).card)
    (hunc : ¬ Colorable G U L) :
    (∀ v ∈ U, degIn G U v = 2) ∧ Odd U.card :=
  two_conn_gallai_aux
    (fun {_ _} h1 h2 => colorable_of_strict_slack _ _ _ rfl h1 h2)
    (fun {_ _} _ h1 {_ _ _} hw hu1 hu2 hw1 hw2 hne hnadj hd1 hd2 hc =>
      colorable_of_cherry h1 hw hu1 hu2 hw1 hw2 hne hnadj hd1 hd2 hc)
    hconn hcard hmax hnk4 h2conn hdeg hunc

def IsBridgeSplit (G : SimpleGraph V) (U A B : Finset V) (y z : V) : Prop :=
  A ∪ B = U ∧ Disjoint A B ∧ ConnIn G A ∧ ConnIn G B ∧
    y ∈ A ∧ z ∈ B ∧ G.Adj y z ∧ ∀ a ∈ A, ∀ b ∈ B, G.Adj a b → a = y ∧ b = z

lemma has_bridge_of_cut {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {y : V}
    (hconn : ConnIn G U) (hmax : ∀ v ∈ U, degIn G U v ≤ 3) (hy : y ∈ U)
    (hcut : ¬ ConnIn G (U.erase y)) :
    ∃ A B z, IsBridgeSplit G U A B y z := by
  classical
  have hnc : ∃ a0 ∈ U.erase y, ∃ b0 ∈ U.erase y, ¬ ReachIn G (U.erase y) a0 b0 := by
    by_contra hall
    push_neg at hall
    exact hcut hall
  obtain ⟨a0, ha0, b0, hb0, hnab⟩ := hnc
  let C1 := (U.erase y).filter (fun v => ReachIn G (U.erase y) a0 v)
  let C2 := (U.erase y) \ C1
  have hC1_sub : C1 ⊆ U.erase y := Finset.filter_subset _ _
  have hC2_sub : C2 ⊆ U.erase y := Finset.sdiff_subset
  have hdisj12 : Disjoint C1 C2 := Finset.disjoint_sdiff
  have ha0C1 : a0 ∈ C1 := Finset.mem_filter.mpr ⟨ha0, Relation.ReflTransGen.refl⟩
  have hb0C2 : b0 ∈ C2 := Finset.mem_sdiff.mpr ⟨hb0, fun h => hnab (Finset.mem_filter.mp h).2⟩
  have hnoedge : ∀ u ∈ C1, ∀ v ∈ C2, ¬ G.Adj u v := by
    intro u hu v hv hadj
    have h1 := Finset.mem_filter.mp hu
    have h2 := Finset.mem_sdiff.mp hv
    apply h2.2
    exact Finset.mem_filter.mpr ⟨h2.1, Relation.ReflTransGen.tail h1.2 ⟨h1.1, h2.1, hadj⟩⟩
  have hconnC1 : ConnIn G C1 := by
    intro u hu v hv
    have hu1 := Finset.mem_filter.mp hu
    have hv1 := Finset.mem_filter.mp hv
    have hpath : ReachIn G (U.erase y) u v :=
      Relation.ReflTransGen.trans (reachIn_symm hu1.2) hv1.2
    have hlift : ∀ x, ReachIn G (U.erase y) u x → ReachIn G C1 u x := by
      intro x hux
      induction hux with
      | refl => exact Relation.ReflTransGen.refl
      | @tail p q hup hpq ih =>
        have hpC1 : p ∈ C1 := Finset.mem_filter.mpr ⟨hpq.1, Relation.ReflTransGen.trans hu1.2 hup⟩
        have hqC1 : q ∈ C1 := Finset.mem_filter.mpr ⟨hpq.2.1, Relation.ReflTransGen.tail (Relation.ReflTransGen.trans hu1.2 hup) hpq⟩
        exact Relation.ReflTransGen.tail ih ⟨hpC1, hqC1, hpq.2.2⟩
    exact hlift v hpath
  have hNy1 : (C1.filter (fun w => G.Adj y w)).Nonempty := by
    rcases reachIn_erase_or_adj_clean ha0 (hconn a0 (Finset.mem_of_mem_erase ha0) y hy) with ⟨hne, _⟩ | ⟨w, hw, hpath, hadj⟩
    · exact absurd rfl hne
    · exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hw, hpath⟩, hadj.symm⟩⟩
  have hNy2 : (C2.filter (fun w => G.Adj y w)).Nonempty := by
    rcases reachIn_erase_or_adj_clean hb0 (hconn b0 (Finset.mem_of_mem_erase hb0) y hy) with ⟨hne, _⟩ | ⟨w, hw, hpath, hadj⟩
    · exact absurd rfl hne
    · have hwC2 : w ∈ C2 := by
        refine Finset.mem_sdiff.mpr ⟨hw, ?_⟩
        intro hw1
        exact hnab (Relation.ReflTransGen.trans (Finset.mem_filter.mp hw1).2 (reachIn_symm hpath))
      exact ⟨w, Finset.mem_filter.mpr ⟨hwC2, hadj.symm⟩⟩
  have hsum : (C1.filter (fun w => G.Adj y w)).card + (C2.filter (fun w => G.Adj y w)).card ≤ 3 := by
    have hunion : (C1.filter (fun w => G.Adj y w)) ∪ (C2.filter (fun w => G.Adj y w)) ⊆ U.filter (fun w => G.Adj y w) := by
      intro w hw
      rcases Finset.mem_union.mp hw with h | h
      · exact Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase (hC1_sub (Finset.mem_filter.mp h).1), (Finset.mem_filter.mp h).2⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase (hC2_sub (Finset.mem_filter.mp h).1), (Finset.mem_filter.mp h).2⟩
    have hdisjF : Disjoint (C1.filter (fun w => G.Adj y w)) (C2.filter (fun w => G.Adj y w)) :=
      hdisj12.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [← Finset.card_union_of_disjoint hdisjF]
    exact le_trans (Finset.card_le_card hunion) (hmax y hy)
  have hc1pos : 1 ≤ (C1.filter (fun w => G.Adj y w)).card := Finset.card_pos.mpr hNy1
  have hc2pos : 1 ≤ (C2.filter (fun w => G.Adj y w)).card := Finset.card_pos.mpr hNy2
  by_cases hc1eq : (C1.filter (fun w => G.Adj y w)).card = 1
  · obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hc1eq
    have hzmem : z ∈ C1.filter (fun w => G.Adj y w) := by rw [hz]; simp
    have hzC1 : z ∈ C1 := (Finset.mem_filter.mp hzmem).1
    have hyz : G.Adj y z := (Finset.mem_filter.mp hzmem).2
    let A := insert y C2
    have hAB : A ∪ C1 = U := by
      ext v
      simp only [A, Finset.mem_union, Finset.mem_insert, C2, Finset.mem_sdiff]
      constructor
      · rintro ((rfl | ⟨hv, _⟩) | hv)
        · exact hy
        · exact Finset.mem_of_mem_erase hv
        · exact Finset.mem_of_mem_erase (hC1_sub hv)
      · intro hv
        by_cases hvy : v = y
        · exact Or.inl (Or.inl hvy)
        · by_cases hv1 : v ∈ C1
          · exact Or.inr hv1
          · exact Or.inl (Or.inr ⟨Finset.mem_erase.mpr ⟨hvy, hv⟩, hv1⟩)
    have hdisjA : Disjoint A C1 := by
      refine Finset.disjoint_left.mpr ?_
      intro v hvA hv1
      rcases Finset.mem_insert.mp hvA with rfl | hv2
      · exact (Finset.mem_erase.mp (hC1_sub hv1)).1 rfl
      · exact (Finset.mem_sdiff.mp hv2).2 hv1
    have hconnA : ConnIn G A := by
      have htoY : ∀ u ∈ A, ReachIn G A u y := by
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu2
        · exact Relation.ReflTransGen.refl
        · have huU : u ∈ U.erase y := hC2_sub hu2
          rcases reachIn_erase_or_adj_clean huU (hconn u (Finset.mem_of_mem_erase huU) y hy) with ⟨hne, _⟩ | ⟨w, hw, hpath, hadj⟩
          · exact absurd rfl hne
          · have hstay : ∀ x, ReachIn G (U.erase y) u x → ReachIn G A u x ∧ x ∈ C2 := by
              intro x hux
              induction hux with
              | refl => exact ⟨Relation.ReflTransGen.refl, hu2⟩
              | @tail p q _ hpq ih =>
                have hq2 : q ∈ C2 := by
                  refine Finset.mem_sdiff.mpr ⟨hpq.2.1, ?_⟩
                  intro hq1
                  exact hnoedge q hq1 p ih.2 (hpq.2.2.symm)
                exact ⟨Relation.ReflTransGen.tail ih.1 ⟨Finset.mem_insert_of_mem ih.2, Finset.mem_insert_of_mem hq2, hpq.2.2⟩, hq2⟩
            have hwA := hstay w hpath
            exact Relation.ReflTransGen.tail hwA.1 ⟨Finset.mem_insert_of_mem hwA.2, Finset.mem_insert_self y C2, hadj⟩
      intro u hu v hv
      exact Relation.ReflTransGen.trans (htoY u hu) (reachIn_symm (htoY v hv))
    refine ⟨A, C1, z, hAB, hdisjA, hconnA, hconnC1, Finset.mem_insert_self y C2, hzC1, hyz, ?_⟩
    intro a ha b hb hadj
    rcases Finset.mem_insert.mp ha with rfl | ha2
    · have hbmem : b ∈ C1.filter (fun w => G.Adj a w) := Finset.mem_filter.mpr ⟨hb, hadj⟩
      rw [hz, Finset.mem_singleton] at hbmem
      exact ⟨rfl, hbmem⟩
    · exact (hnoedge b hb a ha2 (hadj.symm)).elim
  · have hc2eq : (C2.filter (fun w => G.Adj y w)).card = 1 := by omega
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hc2eq
    have hzmem : z ∈ C2.filter (fun w => G.Adj y w) := by rw [hz]; simp
    have hzC2 : z ∈ C2 := (Finset.mem_filter.mp hzmem).1
    have hyz : G.Adj y z := (Finset.mem_filter.mp hzmem).2
    let A := insert y C1
    have hAB : A ∪ C2 = U := by
      ext v
      simp only [A, Finset.mem_union, Finset.mem_insert, C2, Finset.mem_sdiff]
      constructor
      · rintro ((rfl | hv) | ⟨hv, _⟩)
        · exact hy
        · exact Finset.mem_of_mem_erase (hC1_sub hv)
        · exact Finset.mem_of_mem_erase hv
      · intro hv
        by_cases hvy : v = y
        · exact Or.inl (Or.inl hvy)
        · by_cases hv1 : v ∈ C1
          · exact Or.inl (Or.inr hv1)
          · exact Or.inr ⟨Finset.mem_erase.mpr ⟨hvy, hv⟩, hv1⟩
    have hdisjA : Disjoint A C2 := by
      refine Finset.disjoint_left.mpr ?_
      intro v hvA hv2
      rcases Finset.mem_insert.mp hvA with rfl | hv1
      · exact (Finset.mem_erase.mp (hC2_sub hv2)).1 rfl
      · exact (Finset.mem_sdiff.mp hv2).2 hv1
    have hconnA : ConnIn G A := by
      obtain ⟨w1, hw1⟩ := hNy1
      have hw1C1 : w1 ∈ C1 := (Finset.mem_filter.mp hw1).1
      have hyw1 : G.Adj y w1 := (Finset.mem_filter.mp hw1).2
      have htoY : ∀ u ∈ A, ReachIn G A u y := by
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu1
        · exact Relation.ReflTransGen.refl
        · have h1 : ReachIn G A u w1 := reachIn_mono (Finset.subset_insert y C1) (hconnC1 u hu1 w1 hw1C1)
          exact Relation.ReflTransGen.tail h1 ⟨Finset.mem_insert_of_mem hw1C1, Finset.mem_insert_self y C1, hyw1.symm⟩
      intro u hu v hv
      exact Relation.ReflTransGen.trans (htoY u hu) (reachIn_symm (htoY v hv))
    have hconnC2 : ConnIn G C2 := by
      have htoZ : ∀ u ∈ C2, ReachIn G C2 u z := by
        intro u hu
        have huU : u ∈ U.erase y := hC2_sub hu
        rcases reachIn_erase_or_adj_clean huU (hconn u (Finset.mem_of_mem_erase huU) y hy) with ⟨hne, _⟩ | ⟨w, hw, hpath, hadj⟩
        · exact absurd rfl hne
        · have hstay : ∀ x, ReachIn G (U.erase y) u x → ReachIn G C2 u x ∧ x ∈ C2 := by
            intro x hux
            induction hux with
            | refl => exact ⟨Relation.ReflTransGen.refl, hu⟩
            | @tail p q _ hpq ih =>
              have hq2 : q ∈ C2 := by
                refine Finset.mem_sdiff.mpr ⟨hpq.2.1, ?_⟩
                intro hq1
                exact hnoedge q hq1 p ih.2 (hpq.2.2.symm)
              exact ⟨Relation.ReflTransGen.tail ih.1 ⟨ih.2, hq2, hpq.2.2⟩, hq2⟩
          have hw2 := hstay w hpath
          have hwmem : w ∈ C2.filter (fun t => G.Adj y t) := Finset.mem_filter.mpr ⟨hw2.2, hadj.symm⟩
          rw [hz, Finset.mem_singleton] at hwmem
          subst hwmem
          exact hw2.1
      intro u hu v hv
      exact Relation.ReflTransGen.trans (htoZ u hu) (reachIn_symm (htoZ v hv))
    refine ⟨A, C2, z, hAB, hdisjA, hconnA, hconnC2, Finset.mem_insert_self y C1, hzC2, hyz, ?_⟩
    intro a ha b hb hadj
    rcases Finset.mem_insert.mp ha with rfl | ha1
    · have hbmem : b ∈ C2.filter (fun w => G.Adj a w) := Finset.mem_filter.mpr ⟨hb, hadj⟩
      rw [hz, Finset.mem_singleton] at hbmem
      exact ⟨rfl, hbmem⟩
    · exact (hnoedge a ha1 b hb hadj).elim

lemma degIn_bridge_left {G : SimpleGraph V} [DecidableRel G.Adj] {U A B : Finset V} {y z : V}
    (hs : IsBridgeSplit G U A B y z) (v : V) (hv : v ∈ A) :
    degIn G U v = degIn G A v + if v = y then 1 else 0 := by
  unfold degIn
  have hsub : U = A ∪ B := hs.1.symm
  rw [hsub, Finset.filter_union, Finset.card_union_of_disjoint
    (hs.2.1.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  congr 1
  by_cases hvy : v = y
  · subst hvy
    have heq : B.filter (fun w => G.Adj v w) = {z} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro ⟨hw, ha⟩; exact (hs.2.2.2.2.2.2.2 v hv w hw ha).2
      · rintro rfl; exact ⟨hs.2.2.2.2.2.1, hs.2.2.2.2.2.2.1⟩
    rw [heq, Finset.card_singleton, if_pos rfl]
  · have heq : B.filter (fun w => G.Adj v w) = ∅ := by
      ext w
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hw ha
      exact hvy (hs.2.2.2.2.2.2.2 v hv w hw ha).1
    rw [heq, Finset.card_empty, if_neg hvy]

lemma bridge_split_symm {G : SimpleGraph V} {U A B : Finset V} {y z : V}
    (hs : IsBridgeSplit G U A B y z) : IsBridgeSplit G U B A z y := by
  refine ⟨by rw [Finset.union_comm, hs.1], hs.2.1.symm, hs.2.2.2.1, hs.2.2.1,
    hs.2.2.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.2.1.symm, ?_⟩
  intro b hb a ha hadj
  have h := hs.2.2.2.2.2.2.2 a ha b hb (hadj.symm)
  exact ⟨h.2, h.1⟩

def eraseAt (L : V → Finset (Fin 3)) (v0 : V) (c0 : Fin 3) : V → Finset (Fin 3) :=
  fun v => if v = v0 then (L v).erase c0 else L v

def Uncolorable (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) : Prop :=
  ∃ L : V → Finset (Fin 3), (∀ v ∈ U, degIn G U v ≤ (L v).card) ∧ ¬ Colorable G U L

lemma bridge_split_uncolorable {G : SimpleGraph V} [DecidableRel G.Adj] {U A B : Finset V} {y z : V}
    {L : V → Finset (Fin 3)} (hs : IsBridgeSplit G U A B y z)
    (hdeg : ∀ v ∈ U, degIn G U v ≤ (L v).card) (hunc : ¬ Colorable G U L) :
    Uncolorable G A ∧ Uncolorable G B := by
  classical
  let FA := Finset.univ.filter (fun c0 : Fin 3 =>
    ∃ c : V → Fin 3, (∀ v ∈ A, c v ∈ L v) ∧ (∀ u ∈ A, ∀ v ∈ A, G.Adj u v → c u ≠ c v) ∧ c y = c0)
  let FB := Finset.univ.filter (fun c0 : Fin 3 =>
    ∃ c : V → Fin 3, (∀ v ∈ B, c v ∈ L v) ∧ (∀ u ∈ B, ∀ v ∈ B, G.Adj u v → c u ≠ c v) ∧ c z = c0)
  have hA_sub : A ⊆ U := by rw [← hs.1]; exact Finset.subset_union_left
  have hB_sub : B ⊆ U := by rw [← hs.1]; exact Finset.subset_union_right
  have hFA_ne : FA.Nonempty := by
    have hdegA : ∀ v ∈ A, degIn G A v ≤ (L v).card := fun v hv =>
      le_trans (degIn_mono hA_sub v) (hdeg v (hA_sub hv))
    have hslA : ∀ u ∈ A, ∃ r ∈ A, ReachIn G A u r ∧ degIn G A r < (L r).card := by
      intro u hu
      refine ⟨y, hs.2.2.2.2.1, hs.2.2.1 u hu y hs.2.2.2.2.1, ?_⟩
      have hdy := degIn_bridge_left hs y hs.2.2.2.2.1
      have hLy := hdeg y (hA_sub hs.2.2.2.2.1)
      simp at hdy; omega
    obtain ⟨c, hcL, hcadj⟩ := colorable_of_strict_slack A.card A L rfl hdegA hslA
    exact ⟨c y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, hcL, hcadj, rfl⟩⟩
  have hFB_ne : FB.Nonempty := by
    have hs' := bridge_split_symm hs
    have hdegB : ∀ v ∈ B, degIn G B v ≤ (L v).card := fun v hv =>
      le_trans (degIn_mono hB_sub v) (hdeg v (hB_sub hv))
    have hslB : ∀ u ∈ B, ∃ r ∈ B, ReachIn G B u r ∧ degIn G B r < (L r).card := by
      intro u hu
      refine ⟨z, hs.2.2.2.2.2.1, hs.2.2.2.1 u hu z hs.2.2.2.2.2.1, ?_⟩
      have hdz := degIn_bridge_left hs' z hs.2.2.2.2.2.1
      have hLz := hdeg z (hB_sub hs.2.2.2.2.2.1)
      simp at hdz; omega
    obtain ⟨c, hcL, hcadj⟩ := colorable_of_strict_slack B.card B L rfl hdegB hslB
    exact ⟨c z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, hcL, hcadj, rfl⟩⟩
  have hno_diff : ∀ ca ∈ FA, ∀ cb ∈ FB, ca = cb := by
    intro ca hca cb hcb
    by_contra hne
    obtain ⟨cA, hcAL, hcAadj, hcy⟩ := (Finset.mem_filter.mp hca).2
    obtain ⟨cB, hcBL, hcBadj, hcz⟩ := (Finset.mem_filter.mp hcb).2
    apply hunc
    refine ⟨fun v => if v ∈ A then cA v else cB v, ?_, ?_⟩
    · intro v hv
      rw [← hs.1] at hv
      by_cases hvA : v ∈ A
      · simp [hvA, hcAL v hvA]
      · have hvB : v ∈ B := (Finset.mem_union.mp hv).resolve_left hvA
        simp [hvA, hcBL v hvB]
    · intro u hu v hv hadj
      rw [← hs.1] at hu hv
      by_cases huA : u ∈ A <;> by_cases hvA : v ∈ A
      · simp [huA, hvA, hcAadj u huA v hvA hadj]
      · have hvB : v ∈ B := (Finset.mem_union.mp hv).resolve_left hvA
        have ⟨huy, hvz⟩ := hs.2.2.2.2.2.2.2 u huA v hvB hadj
        subst huy; subst hvz
        simp [huA, hvA, hcy, hcz, hne]
      · have huB : u ∈ B := (Finset.mem_union.mp hu).resolve_left huA
        have ⟨hvy, huz⟩ := hs.2.2.2.2.2.2.2 v hvA u huB (hadj.symm)
        subst hvy; subst huz
        simp [huA, hvA, hcy, hcz, Ne.symm hne]
      · have huB : u ∈ B := (Finset.mem_union.mp hu).resolve_left huA
        have hvB : v ∈ B := (Finset.mem_union.mp hv).resolve_left hvA
        simp [huA, hvA, hcBadj u huB v hvB hadj]
  obtain ⟨c0, hc0A⟩ := hFA_ne
  obtain ⟨c1, hc1B⟩ := hFB_ne
  have hc01 : c0 = c1 := hno_diff c0 hc0A c1 hc1B
  subst hc01
  constructor
  · refine ⟨eraseAt L y c0, ?_, ?_⟩
    · intro v hv
      have hdv := degIn_bridge_left hs v hv
      have hLv := hdeg v (hA_sub hv)
      by_cases hvy : v = y
      · subst hvy
        simp only [eraseAt, if_true]
        have her := Finset.pred_card_le_card_erase (s := L v) (a := c0)
        simp at hdv; omega
      · simp only [eraseAt, hvy, if_false]
        simp [hvy] at hdv; omega
    · rintro ⟨c, hcL, hcadj⟩
      have hcy_mem : c y ∈ (L y).erase c0 := by
        have := hcL y hs.2.2.2.2.1
        simpa [eraseAt] using this
      have hcy_ne : c y ≠ c0 := (Finset.mem_erase.mp hcy_mem).1
      have hcyFA : c y ∈ FA := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, ?_, hcadj, rfl⟩
        intro v hv
        have hm := hcL v hv
        by_cases hvy : v = y
        · subst hvy; simp only [eraseAt, if_true] at hm; exact Finset.mem_of_mem_erase hm
        · simpa [eraseAt, hvy] using hm
      exact hcy_ne (hno_diff (c y) hcyFA c0 hc1B)
  · refine ⟨eraseAt L z c0, ?_, ?_⟩
    · intro v hv
      have hdv := degIn_bridge_left (bridge_split_symm hs) v hv
      have hLv := hdeg v (hB_sub hv)
      by_cases hvz : v = z
      · subst hvz
        simp only [eraseAt, if_true]
        have her := Finset.pred_card_le_card_erase (s := L v) (a := c0)
        simp at hdv; omega
      · simp only [eraseAt, hvz, if_false]
        simp [hvz] at hdv; omega
    · rintro ⟨c, hcL, hcadj⟩
      have hcz_mem : c z ∈ (L z).erase c0 := by
        have := hcL z hs.2.2.2.2.2.1
        simpa [eraseAt] using this
      have hcz_ne : c z ≠ c0 := (Finset.mem_erase.mp hcz_mem).1
      have hczFB : c z ∈ FB := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, ?_, hcadj, rfl⟩
        intro v hv
        have hm := hcL v hv
        by_cases hvz : v = z
        · subst hvz; simp only [eraseAt, if_true] at hm; exact Finset.mem_of_mem_erase hm
        · simpa [eraseAt, hvz] using hm
      exact hcz_ne (hno_diff c0 hc0A (c z) hczFB).symm

def pCount (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) : Nat :=
  U.sum (fun v => 3 - degIn G U v)

lemma pCount_bridge_split {G : SimpleGraph V} [DecidableRel G.Adj] {U A B : Finset V} {y z : V}
    (hs : IsBridgeSplit G U A B y z) (hmax : ∀ v ∈ U, degIn G U v ≤ 3) :
    pCount G U + 2 = pCount G A + pCount G B := by
  have hA_sub : A ⊆ U := by rw [← hs.1]; exact Finset.subset_union_left
  have hB_sub : B ⊆ U := by rw [← hs.1]; exact Finset.subset_union_right
  have hsumA : A.sum (fun v => 3 - degIn G U v) + 1 = pCount G A := by
    unfold pCount
    have h1 : A.sum (fun v => 3 - degIn G A v) =
        A.sum (fun v => (3 - degIn G U v) + if v = y then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro v hv
      have hd := degIn_bridge_left hs v hv
      have hm := hmax v (hA_sub hv)
      by_cases hvy : v = y
      · rw [if_pos hvy] at hd ⊢; omega
      · rw [if_neg hvy] at hd ⊢; omega
    rw [h1, Finset.sum_add_distrib, Finset.sum_ite_eq' A y (fun _ => 1), if_pos hs.2.2.2.2.1]
  have hsumB : B.sum (fun v => 3 - degIn G U v) + 1 = pCount G B := by
    unfold pCount
    have hs' := bridge_split_symm hs
    have h1 : B.sum (fun v => 3 - degIn G B v) =
        B.sum (fun v => (3 - degIn G U v) + if v = z then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro v hv
      have hd := degIn_bridge_left hs' v hv
      have hm := hmax v (hB_sub hv)
      by_cases hvz : v = z
      · rw [if_pos hvz] at hd ⊢; omega
      · rw [if_neg hvz] at hd ⊢; omega
    rw [h1, Finset.sum_add_distrib, Finset.sum_ite_eq' B z (fun _ => 1), if_pos hs.2.2.2.2.2.1]
  have hU : pCount G U = A.sum (fun v => 3 - degIn G U v) + B.sum (fun v => 3 - degIn G U v) := by
    unfold pCount
    rw [← hs.1, Finset.sum_union hs.2.1]
  omega

lemma uncolorable_deficit {G : SimpleGraph V} [DecidableRel G.Adj] :
    ∀ n : Nat, ∀ U : Finset V, U.card = n → U.Nonempty → ConnIn G U →
      (∀ v ∈ U, degIn G U v ≤ 3) →
      ¬ (U.card = 4 ∧ ∀ v ∈ U, degIn G U v = 3) →
      Uncolorable G U →
      3 ≤ pCount G U ∧ U.card ≤ 3 * (pCount G U - 2) ∧ Even (3 * (pCount G U - 2) - U.card) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro U hcard hne hconn hmax hnk4 hunc
    by_cases hcut : ∃ y ∈ U, ¬ ConnIn G (U.erase y)
    · obtain ⟨y, hy, hnot⟩ := hcut
      obtain ⟨A, B, z, hs⟩ := has_bridge_of_cut hconn hmax hy hnot
      obtain ⟨L, hdeg, hnc⟩ := hunc
      obtain ⟨huncA, huncB⟩ := bridge_split_uncolorable hs hdeg hnc
      have hA_sub : A ⊆ U := by rw [← hs.1]; exact Finset.subset_union_left
      have hB_sub : B ⊆ U := by rw [← hs.1]; exact Finset.subset_union_right
      have hcardAB : A.card + B.card = U.card := by rw [← hs.1, Finset.card_union_of_disjoint hs.2.1]
      have hA_ne : A.Nonempty := ⟨y, hs.2.2.2.2.1⟩
      have hB_ne : B.Nonempty := ⟨z, hs.2.2.2.2.2.1⟩
      have hA_lt : A.card < n := by have := Finset.card_pos.mpr hB_ne; omega
      have hB_lt : B.card < n := by have := Finset.card_pos.mpr hA_ne; omega
      have hmaxA : ∀ v ∈ A, degIn G A v ≤ 3 := fun v hv => le_trans (degIn_mono hA_sub v) (hmax v (hA_sub hv))
      have hmaxB : ∀ v ∈ B, degIn G B v ≤ 3 := fun v hv => le_trans (degIn_mono hB_sub v) (hmax v (hB_sub hv))
      have hnk4A : ¬ (A.card = 4 ∧ ∀ v ∈ A, degIn G A v = 3) := by
        rintro ⟨_, hall⟩
        have hdy := degIn_bridge_left hs y hs.2.2.2.2.1
        have hmy := hmax y (hA_sub hs.2.2.2.2.1)
        have h3 := hall y hs.2.2.2.2.1
        simp at hdy; omega
      have hnk4B : ¬ (B.card = 4 ∧ ∀ v ∈ B, degIn G B v = 3) := by
        rintro ⟨_, hall⟩
        have hdz := degIn_bridge_left (bridge_split_symm hs) z hs.2.2.2.2.2.1
        have hmz := hmax z (hB_sub hs.2.2.2.2.2.1)
        have h3 := hall z hs.2.2.2.2.2.1
        simp at hdz; omega
      obtain ⟨hpA, hleA, ⟨mA, hmA⟩⟩ := ih A.card hA_lt A rfl hA_ne hs.2.2.1 hmaxA hnk4A huncA
      obtain ⟨hpB, hleB, ⟨mB, hmB⟩⟩ := ih B.card hB_lt B rfl hB_ne hs.2.2.2.1 hmaxB hnk4B huncB
      have hpU := pCount_bridge_split hs hmax
      refine ⟨by omega, by omega, ⟨mA + mB, by omega⟩⟩
    · push_neg at hcut
      by_cases hc1 : U.card = 1
      · obtain ⟨v0, rfl⟩ := Finset.card_eq_one.mp hc1
        have hd0 : degIn G {v0} v0 = 0 := by
          unfold degIn
          have : ({v0} : Finset V).filter (fun w => G.Adj v0 w) = ∅ := by
            ext w; simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
            rintro rfl ha; exact G.ne_of_adj ha rfl
          rw [this, Finset.card_empty]
        have hp : pCount G {v0} = 3 := by simp [pCount, hd0]
        rw [hp, Finset.card_singleton]
        exact ⟨by omega, by omega, ⟨1, by omega⟩⟩
      · by_cases hc2 : U.card = 2
        · obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hc2
          have hadj : G.Adj u v := by
            have hr := hconn u (by simp) v (by simp)
            rcases Relation.ReflTransGen.cases_head hr with h | ⟨w, huw, _⟩
            · exact absurd h huv
            · rcases Finset.mem_insert.mp huw.2.1 with rfl | hw
              · exact (G.ne_of_adj huw.2.2 rfl).elim
              · rw [Finset.mem_singleton.mp hw] at huw; exact huw.2.2
          have hdu : degIn G {u, v} u = 1 := by
            unfold degIn
            have : ({u, v} : Finset V).filter (fun w => G.Adj u w) = {v} := by
              ext w; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨rfl | rfl, ha⟩
                · exact (G.ne_of_adj ha rfl).elim
                · rfl
              · rintro rfl; exact ⟨Or.inr rfl, hadj⟩
            rw [this, Finset.card_singleton]
          have hdv : degIn G {u, v} v = 1 := by
            unfold degIn
            have : ({u, v} : Finset V).filter (fun w => G.Adj v w) = {u} := by
              ext w; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨rfl | rfl, ha⟩
                · rfl
                · exact (G.ne_of_adj ha rfl).elim
              · rintro rfl; exact ⟨Or.inl rfl, hadj.symm⟩
            rw [this, Finset.card_singleton]
          have hp : pCount G {u, v} = 4 := by
            simp [pCount, Finset.sum_pair huv, hdu, hdv]
          have hcard2 : ({u, v} : Finset V).card = 2 := Finset.card_pair huv
          rw [hp, hcard2]
          exact ⟨by omega, by omega, ⟨2, by omega⟩⟩
        · have hc3 : 3 ≤ U.card := by have := Finset.card_pos.mpr hne; omega
          obtain ⟨L, hdeg, hnc⟩ := hunc
          obtain ⟨h2reg, ⟨m, hm⟩⟩ := two_conn_gallai hconn hc3 hmax hnk4 hcut hdeg hnc
          have hp : pCount G U = U.card := by
            unfold pCount
            calc U.sum (fun v => 3 - degIn G U v) = U.sum (fun _ => 1) := by
                  apply Finset.sum_congr rfl; intro v hv; rw [h2reg v hv]
              _ = U.card := by simp
          rw [hp]
          refine ⟨by omega, by omega, ⟨U.card - 3, by omega⟩⟩

end GraphHelpers2

section DeficitChar

variable {V : Type*} [DecidableEq V] [Fintype V]

def Forb (f : V → Option (Fin 3)) (v : V) : Finset (Fin 3) :=
  match f v with
  | none => Finset.univ
  | some b => Finset.univ.erase b

lemma forb_card_ge_two (f : V → Option (Fin 3)) (v : V) : 2 ≤ (Forb f v).card := by
  unfold Forb
  cases f v with
  | none => decide
  | some b =>
    dsimp only
    rw [Finset.card_erase_of_mem (Finset.mem_univ b)]
    decide

lemma triangle_forb_char (a : Fin 3) (fu fw : Option (Fin 3)) :
    (∃ cu cw : Fin 3, (∀ b, fu = some b → cu ≠ b) ∧ (∀ b, fw = some b → cw ≠ b) ∧
      cu ≠ a ∧ cw ≠ a ∧ cu ≠ cw) ↔
    ¬ (∃ b : Fin 3, b ≠ a ∧ fu = some b ∧ fw = some b) := by
  fin_cases a <;> cases fu with
  | none =>
    cases fw with
    | none => decide
    | some w => fin_cases w <;> decide
  | some u =>
    fin_cases u <;> cases fw with
    | none => decide
    | some w => fin_cases w <;> decide

lemma zero_deficit_deg_ge_two {G : SimpleGraph V} [DecidableRel G.Adj] :
    ∀ n : Nat, ∀ U : Finset V, U.card = n → U.Nonempty → ConnIn G U →
      (∀ v ∈ U, degIn G U v ≤ 3) →
      ¬ (U.card = 4 ∧ ∀ v ∈ U, degIn G U v = 3) →
      Uncolorable G U → 3 * (pCount G U - 2) = U.card →
      ∀ v ∈ U, 2 ≤ degIn G U v := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro U hcard hne hconn hmax hnk4 hunc hdef
    by_cases hcut : ∃ y ∈ U, ¬ ConnIn G (U.erase y)
    · obtain ⟨y, hy, hnot⟩ := hcut
      obtain ⟨A, B, z, hs⟩ := has_bridge_of_cut hconn hmax hy hnot
      obtain ⟨L, hdeg, hnc⟩ := hunc
      obtain ⟨huncA, huncB⟩ := bridge_split_uncolorable hs hdeg hnc
      have hA_sub : A ⊆ U := by rw [← hs.1]; exact Finset.subset_union_left
      have hB_sub : B ⊆ U := by rw [← hs.1]; exact Finset.subset_union_right
      have hcardAB : A.card + B.card = U.card := by rw [← hs.1, Finset.card_union_of_disjoint hs.2.1]
      have hA_ne : A.Nonempty := ⟨y, hs.2.2.2.2.1⟩
      have hB_ne : B.Nonempty := ⟨z, hs.2.2.2.2.2.1⟩
      have hA_lt : A.card < n := by have := Finset.card_pos.mpr hB_ne; omega
      have hB_lt : B.card < n := by have := Finset.card_pos.mpr hA_ne; omega
      have hmaxA : ∀ v ∈ A, degIn G A v ≤ 3 := fun v hv => le_trans (degIn_mono hA_sub v) (hmax v (hA_sub hv))
      have hmaxB : ∀ v ∈ B, degIn G B v ≤ 3 := fun v hv => le_trans (degIn_mono hB_sub v) (hmax v (hB_sub hv))
      have hnk4A : ¬ (A.card = 4 ∧ ∀ v ∈ A, degIn G A v = 3) := by
        rintro ⟨_, hall⟩
        have hdy := degIn_bridge_left hs y hs.2.2.2.2.1
        have hmy := hmax y (hA_sub hs.2.2.2.2.1)
        have h3 := hall y hs.2.2.2.2.1
        simp at hdy; omega
      have hnk4B : ¬ (B.card = 4 ∧ ∀ v ∈ B, degIn G B v = 3) := by
        rintro ⟨_, hall⟩
        have hdz := degIn_bridge_left (bridge_split_symm hs) z hs.2.2.2.2.2.1
        have hmz := hmax z (hB_sub hs.2.2.2.2.2.1)
        have h3 := hall z hs.2.2.2.2.2.1
        simp at hdz; omega
      obtain ⟨hpA, hleA, _⟩ := uncolorable_deficit A.card A rfl hA_ne hs.2.2.1 hmaxA hnk4A huncA
      obtain ⟨hpB, hleB, _⟩ := uncolorable_deficit B.card B rfl hB_ne hs.2.2.2.1 hmaxB hnk4B huncB
      have hpU := pCount_bridge_split hs hmax
      have hdefA : 3 * (pCount G A - 2) = A.card := by omega
      have hdefB : 3 * (pCount G B - 2) = B.card := by omega
      have hgeA := ih A.card hA_lt A rfl hA_ne hs.2.2.1 hmaxA hnk4A huncA hdefA
      have hgeB := ih B.card hB_lt B rfl hB_ne hs.2.2.2.1 hmaxB hnk4B huncB hdefB
      intro v hv
      rw [← hs.1] at hv
      rcases Finset.mem_union.mp hv with hvA | hvB
      · exact le_trans (hgeA v hvA) (degIn_mono hA_sub v)
      · exact le_trans (hgeB v hvB) (degIn_mono hB_sub v)
    · push_neg at hcut
      by_cases hc1 : U.card = 1
      · obtain ⟨v0, rfl⟩ := Finset.card_eq_one.mp hc1
        have hd0 : degIn G {v0} v0 = 0 := by
          unfold degIn
          have : ({v0} : Finset V).filter (fun w => G.Adj v0 w) = ∅ := by
            ext w; simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
            rintro rfl ha; exact G.ne_of_adj ha rfl
          rw [this, Finset.card_empty]
        have hp : pCount G {v0} = 3 := by simp [pCount, hd0]
        rw [hp, Finset.card_singleton] at hdef; omega
      · by_cases hc2 : U.card = 2
        · obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hc2
          have hadj : G.Adj u v := by
            have hr := hconn u (by simp) v (by simp)
            rcases Relation.ReflTransGen.cases_head hr with h | ⟨w, huw, _⟩
            · exact absurd h huv
            · rcases Finset.mem_insert.mp huw.2.1 with rfl | hw
              · exact (G.ne_of_adj huw.2.2 rfl).elim
              · rw [Finset.mem_singleton.mp hw] at huw; exact huw.2.2
          have hdu : degIn G {u, v} u = 1 := by
            unfold degIn
            have : ({u, v} : Finset V).filter (fun w => G.Adj u w) = {v} := by
              ext w; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨rfl | rfl, ha⟩
                · exact (G.ne_of_adj ha rfl).elim
                · rfl
              · rintro rfl; exact ⟨Or.inr rfl, hadj⟩
            rw [this, Finset.card_singleton]
          have hdv : degIn G {u, v} v = 1 := by
            unfold degIn
            have : ({u, v} : Finset V).filter (fun w => G.Adj v w) = {u} := by
              ext w; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨rfl | rfl, ha⟩
                · rfl
                · exact (G.ne_of_adj ha rfl).elim
              · rintro rfl; exact ⟨Or.inl rfl, hadj.symm⟩
            rw [this, Finset.card_singleton]
          have hp : pCount G {u, v} = 4 := by simp [pCount, Finset.sum_pair huv, hdu, hdv]
          have hcard2 : ({u, v} : Finset V).card = 2 := Finset.card_pair huv
          rw [hp, hcard2] at hdef; omega
        · have hc3 : 3 ≤ U.card := by have := Finset.card_pos.mpr hne; omega
          obtain ⟨L, hdeg, hnc⟩ := hunc
          obtain ⟨h2reg, _⟩ := two_conn_gallai hconn hc3 hmax hnk4 hcut hdeg hnc
          intro v hv
          rw [h2reg v hv]

lemma zero_deficit_char {G : SimpleGraph V} [DecidableRel G.Adj] :
    ∀ n : Nat, ∀ U : Finset V, U.card = n → U.Nonempty → ConnIn G U →
      (∀ v ∈ U, degIn G U v ≤ 3) →
      ¬ (U.card = 4 ∧ ∀ v ∈ U, degIn G U v = 3) →
      Uncolorable G U → 3 * (pCount G U - 2) = U.card →
      ∀ r ∈ U, degIn G U r = 2 →
      let T := U.filter (fun v => v ≠ r ∧ degIn G U v = 2)
      T.Nonempty ∧
      ∀ (f : V → Option (Fin 3)), f r = none → (∀ v ∈ U, degIn G U v = 3 → f v = none) →
      ∀ a : Fin 3,
        (∃ c : V → Fin 3, (∀ v ∈ U, c v ∈ Forb f v) ∧
          (∀ u ∈ U, ∀ v ∈ U, G.Adj u v → c u ≠ c v) ∧ c r = a) ↔
        ¬ (∃ b : Fin 3, b ≠ a ∧ ∀ v ∈ T, f v = some b) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro U hcard hne hconn hmax hnk4 hunc hdef r hr hdr
    dsimp only
    by_cases hcut : ∃ y ∈ U, ¬ ConnIn G (U.erase y)
    · obtain ⟨y0, hy0, hnot⟩ := hcut
      obtain ⟨A0, B0, z0, hs0⟩ := has_bridge_of_cut hconn hmax hy0 hnot
      have hsplit : ∃ A B y z, IsBridgeSplit G U A B y z ∧ r ∈ A := by
        have hrAB : r ∈ A0 ∪ B0 := by rw [hs0.1]; exact hr
        rcases Finset.mem_union.mp hrAB with hrA | hrB
        · exact ⟨A0, B0, y0, z0, hs0, hrA⟩
        · exact ⟨B0, A0, z0, y0, bridge_split_symm hs0, hrB⟩
      obtain ⟨A, B, y, z, hs, hrA⟩ := hsplit
      obtain ⟨L, hdeg, hnc⟩ := hunc
      obtain ⟨huncA, huncB⟩ := bridge_split_uncolorable hs hdeg hnc
      have hA_sub : A ⊆ U := by rw [← hs.1]; exact Finset.subset_union_left
      have hB_sub : B ⊆ U := by rw [← hs.1]; exact Finset.subset_union_right
      have hcardAB : A.card + B.card = U.card := by rw [← hs.1, Finset.card_union_of_disjoint hs.2.1]
      have hA_ne : A.Nonempty := ⟨y, hs.2.2.2.2.1⟩
      have hB_ne : B.Nonempty := ⟨z, hs.2.2.2.2.2.1⟩
      have hA_lt : A.card < n := by have := Finset.card_pos.mpr hB_ne; omega
      have hB_lt : B.card < n := by have := Finset.card_pos.mpr hA_ne; omega
      have hmaxA : ∀ v ∈ A, degIn G A v ≤ 3 := fun v hv => le_trans (degIn_mono hA_sub v) (hmax v (hA_sub hv))
      have hmaxB : ∀ v ∈ B, degIn G B v ≤ 3 := fun v hv => le_trans (degIn_mono hB_sub v) (hmax v (hB_sub hv))
      have hnk4A : ¬ (A.card = 4 ∧ ∀ v ∈ A, degIn G A v = 3) := by
        rintro ⟨_, hall⟩
        have hdy := degIn_bridge_left hs y hs.2.2.2.2.1
        have hmy := hmax y (hA_sub hs.2.2.2.2.1)
        have h3 := hall y hs.2.2.2.2.1
        simp at hdy; omega
      have hnk4B : ¬ (B.card = 4 ∧ ∀ v ∈ B, degIn G B v = 3) := by
        rintro ⟨_, hall⟩
        have hdz := degIn_bridge_left (bridge_split_symm hs) z hs.2.2.2.2.2.1
        have hmz := hmax z (hB_sub hs.2.2.2.2.2.1)
        have h3 := hall z hs.2.2.2.2.2.1
        simp at hdz; omega
      obtain ⟨hpA, hleA, _⟩ := uncolorable_deficit A.card A rfl hA_ne hs.2.2.1 hmaxA hnk4A huncA
      obtain ⟨hpB, hleB, _⟩ := uncolorable_deficit B.card B rfl hB_ne hs.2.2.2.1 hmaxB hnk4B huncB
      have hpU := pCount_bridge_split hs hmax
      have hdefA : 3 * (pCount G A - 2) = A.card := by omega
      have hdefB : 3 * (pCount G B - 2) = B.card := by omega
      have hgeA := zero_deficit_deg_ge_two A.card A rfl hA_ne hs.2.2.1 hmaxA hnk4A huncA hdefA
      have hgeB := zero_deficit_deg_ge_two B.card B rfl hB_ne hs.2.2.2.1 hmaxB hnk4B huncB hdefB
      have hdyU := degIn_bridge_left hs y hs.2.2.2.2.1
      have hdzU := degIn_bridge_left (bridge_split_symm hs) z hs.2.2.2.2.2.1
      have hdyA : degIn G A y = 2 := by
        have h1 := hgeA y hs.2.2.2.2.1
        have h2 := hmax y (hA_sub hs.2.2.2.2.1)
        simp at hdyU; omega
      have hdzB : degIn G B z = 2 := by
        have h1 := hgeB z hs.2.2.2.2.2.1
        have h2 := hmax z (hB_sub hs.2.2.2.2.2.1)
        simp at hdzU; omega
      have hry : r ≠ y := by
        intro heq; subst heq; simp at hdyU; omega
      have hdrA : degIn G A r = 2 := by
        have h := degIn_bridge_left hs r hrA
        simp [hry] at h; omega
      obtain ⟨hTA_ne, hcharA⟩ := ih A.card hA_lt A rfl hA_ne hs.2.2.1 hmaxA hnk4A huncA hdefA r hrA hdrA
      obtain ⟨hTB_ne, hcharB⟩ := ih B.card hB_lt B rfl hB_ne hs.2.2.2.1 hmaxB hnk4B huncB hdefB z hs.2.2.2.2.2.1 hdzB
      let TU := U.filter (fun v => v ≠ r ∧ degIn G U v = 2)
      let TA := A.filter (fun v => v ≠ r ∧ degIn G A v = 2)
      let TB := B.filter (fun v => v ≠ z ∧ degIn G B v = 2)
      have hTB_sub : TB ⊆ TU := by
        intro v hv
        have ⟨hvB, hvz, hdvB⟩ := Finset.mem_filter.mp hv
        have hdvU := degIn_bridge_left (bridge_split_symm hs) v hvB
        simp [hvz] at hdvU
        have hvr : v ≠ r := fun heq => Finset.disjoint_left.mp hs.2.1 hrA (heq ▸ hvB)
        exact Finset.mem_filter.mpr ⟨hB_sub hvB, hvr, by omega⟩
      have hTU_ne : TU.Nonempty := hTB_ne.mono hTB_sub
      refine ⟨hTU_ne, ?_⟩
      intro f hfr hf3 a
      have hfz : f z = none := hf3 z (hB_sub hs.2.2.2.2.2.1) (by simp at hdzU; omega)
      have hfy : f y = none := hf3 y (hA_sub hs.2.2.2.2.1) (by simp at hdyU; omega)
      have hf3B : ∀ v ∈ B, degIn G B v = 3 → f v = none := by
        intro v hv hdv
        have hdU := degIn_bridge_left (bridge_split_symm hs) v hv
        have hm := hmax v (hB_sub hv)
        exact hf3 v (hB_sub hv) (by omega)
      classical
      let f' : V → Option (Fin 3) := fun v =>
        if v = y then
          if h : ∃ b : Fin 3, ∀ w ∈ TB, f w = some b then some (Classical.choose h) else none
        else f v
      have hB_forb : ∀ cy : Fin 3,
          (∃ cB : V → Fin 3, (∀ v ∈ B, cB v ∈ Forb f v) ∧
            (∀ u ∈ B, ∀ v ∈ B, G.Adj u v → cB u ≠ cB v) ∧ cB z ≠ cy) ↔ cy ∈ Forb f' y := by
        intro cy
        constructor
        · rintro ⟨cB, hcBL, hcBadj, hcBne⟩
          by_cases hex : ∃ b : Fin 3, ∀ w ∈ TB, f w = some b
          · have hch := Classical.choose_spec hex
            have hne : cy ≠ Classical.choose hex := by
              intro heq
              subst heq
              have hnotB := (hcharB f hfz hf3B (cB z)).mp ⟨cB, hcBL, hcBadj, rfl⟩
              exact hnotB ⟨Classical.choose hex, Ne.symm hcBne, hch⟩
            simp [f', Forb, hex, hne]
          · simp [f', Forb, hex]
        · intro hcy
          by_cases hex : ∃ b : Fin 3, ∀ w ∈ TB, f w = some b
          · have hch := Classical.choose_spec hex
            simp only [f', if_true, hex, dif_pos, Forb, Finset.mem_erase, Finset.mem_univ, and_true] at hcy
            have hBex : ∃ cB : V → Fin 3, (∀ v ∈ B, cB v ∈ Forb f v) ∧
                (∀ u ∈ B, ∀ v ∈ B, G.Adj u v → cB u ≠ cB v) ∧ cB z = Classical.choose hex := by
              rw [hcharB f hfz hf3B (Classical.choose hex)]
              rintro ⟨b, hba, hall⟩
              obtain ⟨w0, hw0⟩ := hTB_ne
              have h1 := hch w0 hw0
              have h2 := hall w0 hw0
              rw [h1] at h2
              exact hba (Option.some.inj h2.symm)
            obtain ⟨cB, hcBL, hcBadj, hcBz⟩ := hBex
            exact ⟨cB, hcBL, hcBadj, by rw [hcBz]; exact Ne.symm hcy⟩
          · obtain ⟨cz, hcz⟩ : ∃ cz : Fin 3, cz ≠ cy := by
              fin_cases cy
              · exact ⟨1, by decide⟩
              · exact ⟨0, by decide⟩
              · exact ⟨0, by decide⟩
            have hBex : ∃ cB : V → Fin 3, (∀ v ∈ B, cB v ∈ Forb f v) ∧
                (∀ u ∈ B, ∀ v ∈ B, G.Adj u v → cB u ≠ cB v) ∧ cB z = cz := by
              rw [hcharB f hfz hf3B cz]
              rintro ⟨b, _, hall⟩
              exact hex ⟨b, hall⟩
            obtain ⟨cB, hcBL, hcBadj, hcBz⟩ := hBex
            exact ⟨cB, hcBL, hcBadj, by rw [hcBz]; exact hcz⟩
      have hfr' : f' r = none := by simp [f', hry, hfr]
      have hf3A' : ∀ v ∈ A, degIn G A v = 3 → f' v = none := by
        intro v hv hdv
        have hvy : v ≠ y := fun heq => by subst heq; omega
        have hdU := degIn_bridge_left hs v hv
        simp [f', hvy]
        exact hf3 v (hA_sub hv) (by simp [hvy] at hdU; omega)
      have hcol_iff : (∃ c : V → Fin 3, (∀ v ∈ U, c v ∈ Forb f v) ∧
            (∀ u ∈ U, ∀ v ∈ U, G.Adj u v → c u ≠ c v) ∧ c r = a) ↔
          (∃ cA : V → Fin 3, (∀ v ∈ A, cA v ∈ Forb f' v) ∧
            (∀ u ∈ A, ∀ v ∈ A, G.Adj u v → cA u ≠ cA v) ∧ cA r = a) := by
        constructor
        · rintro ⟨c, hcL, hcadj, hcr⟩
          refine ⟨c, ?_, fun u hu v hv ha => hcadj u (hA_sub hu) v (hA_sub hv) ha, hcr⟩
          intro v hv
          by_cases hvy : v = y
          · subst hvy
            exact (hB_forb (c v)).mp ⟨c, fun w hw => hcL w (hB_sub hw),
              fun u hu w hw ha => hcadj u (hB_sub hu) w (hB_sub hw) ha,
              hcadj z (hB_sub hs.2.2.2.2.2.1) v (hA_sub hs.2.2.2.2.1) (hs.2.2.2.2.2.2.1.symm)⟩
          · have heq : f' v = f v := by simp [f', hvy]
            rw [Forb, heq]
            exact hcL v (hA_sub hv)
        · rintro ⟨cA, hcAL, hcAadj, hcAr⟩
          obtain ⟨cB, hcBL, hcBadj, hcBne⟩ := (hB_forb (cA y)).mpr (hcAL y hs.2.2.2.2.1)
          refine ⟨fun v => if v ∈ A then cA v else cB v, ?_, ?_, by simp [hrA, hcAr]⟩
          · intro v hv
            rw [← hs.1] at hv
            by_cases hvA : v ∈ A
            · simp only [hvA, if_true]
              by_cases hvy : v = y
              · subst hvy; simp [Forb, hfy]
              · have hm := hcAL v hvA
                have heq : f' v = f v := by simp [f', hvy]
                rwa [Forb, heq] at hm
            · have hvB : v ∈ B := (Finset.mem_union.mp hv).resolve_left hvA
              simp [hvA, hcBL v hvB]
          · intro u hu v hv hadj
            rw [← hs.1] at hu hv
            by_cases huA : u ∈ A <;> by_cases hvA : v ∈ A
            · simp [huA, hvA, hcAadj u huA v hvA hadj]
            · have hvB : v ∈ B := (Finset.mem_union.mp hv).resolve_left hvA
              have ⟨huy, hvz⟩ := hs.2.2.2.2.2.2.2 u huA v hvB hadj
              subst huy; subst hvz
              simp [huA, hvA, Ne.symm hcBne]
            · have huB : u ∈ B := (Finset.mem_union.mp hu).resolve_left huA
              have ⟨hvy, huz⟩ := hs.2.2.2.2.2.2.2 v hvA u huB (hadj.symm)
              subst hvy; subst huz
              simp [huA, hvA, hcBne]
            · have huB : u ∈ B := (Finset.mem_union.mp hu).resolve_left huA
              have hvB : v ∈ B := (Finset.mem_union.mp hv).resolve_left hvA
              simp [huA, hvA, hcBadj u huB v hvB hadj]
      rw [hcol_iff, hcharA f' hfr' hf3A' a]
      have hiff_all : ∀ b : Fin 3, (∀ v ∈ TA, f' v = some b) ↔ (∀ v ∈ TU, f v = some b) := by
        intro b
        constructor
        · intro hallA v hvU
          have ⟨hv, hvr, hdvU⟩ := Finset.mem_filter.mp hvU
          rw [← hs.1] at hv
          rcases Finset.mem_union.mp hv with hvA | hvB
          · have hvy : v ≠ y := fun heq => by subst heq; simp at hdyU; omega
            have hdvA : degIn G A v = 2 := by
              have h := degIn_bridge_left hs v hvA; simp [hvy] at h; omega
            have hm := hallA v (Finset.mem_filter.mpr ⟨hvA, hvr, hdvA⟩)
            simpa [f', hvy] using hm
          · have hvz : v ≠ z := fun heq => by subst heq; simp at hdzU; omega
            have hdvB : degIn G B v = 2 := by
              have h := degIn_bridge_left (bridge_split_symm hs) v hvB; simp [hvz] at h; omega
            have hyTA : y ∈ TA := Finset.mem_filter.mpr ⟨hs.2.2.2.2.1, hry.symm, hdyA⟩
            have hfy' := hallA y hyTA
            by_cases hex : ∃ b0 : Fin 3, ∀ w ∈ TB, f w = some b0
            · simp only [f', if_true, hex, dif_pos] at hfy'
              have hbeq : Classical.choose hex = b := Option.some.inj hfy'
              rw [← hbeq]
              exact Classical.choose_spec hex v (Finset.mem_filter.mpr ⟨hvB, hvz, hdvB⟩)
            · simp [f', hex] at hfy'
        · intro hallU v hvA
          have ⟨hv, hvr, hdvA⟩ := Finset.mem_filter.mp hvA
          by_cases hvy : v = y
          · subst hvy
            have hex : ∃ b0 : Fin 3, ∀ w ∈ TB, f w = some b0 := ⟨b, fun w hw => hallU w (hTB_sub hw)⟩
            simp only [f', if_true, hex, dif_pos]
            obtain ⟨w0, hw0⟩ := hTB_ne
            have h1 := Classical.choose_spec hex w0 hw0
            have h2 := hallU w0 (hTB_sub hw0)
            rw [h1] at h2
            exact h2
          · have hdvU : degIn G U v = 2 := by
              have h := degIn_bridge_left hs v hv; simp [hvy] at h; omega
            simp only [f', hvy, if_false]
            exact hallU v (Finset.mem_filter.mpr ⟨hA_sub hv, hvr, hdvU⟩)
      exact not_congr ⟨fun ⟨b, hba, h⟩ => ⟨b, hba, (hiff_all b).mp h⟩,
        fun ⟨b, hba, h⟩ => ⟨b, hba, (hiff_all b).mpr h⟩⟩
    · push_neg at hcut
      have hge2 := zero_deficit_deg_ge_two U.card U rfl hne hconn hmax hnk4 hunc hdef
      have hc3 : 3 ≤ U.card := by
        obtain ⟨L, hdeg, hnc⟩ := hunc
        have hlt : 2 < U.card := by
          by_contra hle
          have h1 : degIn G U r < U.card := by
            unfold degIn
            have hss : U.filter (fun w => G.Adj r w) ⊂ U := by
              refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
              intro heq
              have : r ∈ U.filter (fun w => G.Adj r w) := heq.symm ▸ hr
              exact G.ne_of_adj (Finset.mem_filter.mp this).2 rfl
            exact Finset.card_lt_card hss
          omega
        omega
      obtain ⟨L, hdeg, hnc⟩ := hunc
      obtain ⟨h2reg, _⟩ := two_conn_gallai hconn hc3 hmax hnk4 hcut hdeg hnc
      have hpU : pCount G U = U.card := by
        unfold pCount
        calc U.sum (fun v => 3 - degIn G U v) = U.sum (fun _ => 1) := by
              apply Finset.sum_congr rfl; intro v hv; rw [h2reg v hv]
          _ = U.card := by simp
      have hU3 : U.card = 3 := by omega
      have hUer2 : (U.erase r).card = 2 := by rw [Finset.card_erase_of_mem hr]; omega
      obtain ⟨u, w, huw, hUer⟩ := Finset.card_eq_two.mp hUer2
      have hUeq : U = {r, u, w} := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases hxr : x = r
        · subst hxr; simp [hr]
        · have : x ∈ U.erase r ↔ x = u ∨ x = w := by rw [hUer]; simp
          simp [hxr, ← this, Finset.mem_erase]
      have hur : u ≠ r := (Finset.mem_erase.mp (by rw [hUer]; simp : u ∈ U.erase r)).1
      have hwr : w ≠ r := (Finset.mem_erase.mp (by rw [hUer]; simp : w ∈ U.erase r)).1
      have huU : u ∈ U := by rw [hUeq]; simp
      have hwU : w ∈ U := by rw [hUeq]; simp
      have hT_eq : U.filter (fun v => v ≠ r ∧ degIn G U v = 2) = {u, w} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro ⟨hx, hxr, _⟩
          have : x ∈ U.erase r := Finset.mem_erase.mpr ⟨hxr, hx⟩
          rw [hUer] at this; simpa using this
        · rintro (rfl | rfl)
          · exact ⟨huU, hur, h2reg x huU⟩
          · exact ⟨hwU, hwr, h2reg x hwU⟩
      have hadj_ru : G.Adj r u := by
        have hsub : U.filter (fun x => G.Adj r x) ⊆ U.erase r := by
          intro x hx
          exact Finset.mem_erase.mpr ⟨G.ne_of_adj (Finset.mem_filter.mp hx).2.symm, (Finset.mem_filter.mp hx).1⟩
        have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hUer2]; exact hdr.ge)
        have : u ∈ U.filter (fun x => G.Adj r x) := by rw [heq, hUer]; simp
        exact (Finset.mem_filter.mp this).2
      have hadj_rw : G.Adj r w := by
        have hsub : U.filter (fun x => G.Adj r x) ⊆ U.erase r := by
          intro x hx
          exact Finset.mem_erase.mpr ⟨G.ne_of_adj (Finset.mem_filter.mp hx).2.symm, (Finset.mem_filter.mp hx).1⟩
        have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hUer2]; exact hdr.ge)
        have : w ∈ U.filter (fun x => G.Adj r x) := by rw [heq, hUer]; simp
        exact (Finset.mem_filter.mp this).2
      have hadj_uw : G.Adj u w := by
        have hsub : U.filter (fun x => G.Adj u x) ⊆ U.erase u := by
          intro x hx
          exact Finset.mem_erase.mpr ⟨G.ne_of_adj (Finset.mem_filter.mp hx).2.symm, (Finset.mem_filter.mp hx).1⟩
        have hcardEu : (U.erase u).card = 2 := by rw [Finset.card_erase_of_mem huU]; omega
        have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcardEu]; exact (h2reg u huU).ge)
        have : w ∈ U.filter (fun x => G.Adj u x) := by
          rw [heq]; exact Finset.mem_erase.mpr ⟨huw.symm, hwU⟩
        exact (Finset.mem_filter.mp this).2
      refine ⟨by rw [hT_eq]; exact ⟨u, by simp⟩, ?_⟩
      intro f hfr _ a
      rw [hT_eq]
      have h1 : (∃ c : V → Fin 3, (∀ v ∈ U, c v ∈ Forb f v) ∧
            (∀ x ∈ U, ∀ y ∈ U, G.Adj x y → c x ≠ c y) ∧ c r = a) ↔
          (∃ cu cw : Fin 3, (∀ b, f u = some b → cu ≠ b) ∧ (∀ b, f w = some b → cw ≠ b) ∧
            cu ≠ a ∧ cw ≠ a ∧ cu ≠ cw) := by
        constructor
        · rintro ⟨c, hcL, hcadj, hcr⟩
          refine ⟨c u, c w, ?_, ?_, ?_, ?_, hcadj u huU w hwU hadj_uw⟩
          · intro b hfu
            have hm := hcL u huU
            simp [Forb, hfu] at hm; exact hm
          · intro b hfw
            have hm := hcL w hwU
            simp [Forb, hfw] at hm; exact hm
          · rw [← hcr]; exact hcadj u huU r hr (hadj_ru.symm)
          · rw [← hcr]; exact hcadj w hwU r hr (hadj_rw.symm)
        · rintro ⟨cu, cw, hcu, hcw, hcua, hcwa, hcuw⟩
          let c : V → Fin 3 := fun x => if x = r then a else if x = u then cu else cw
          refine ⟨c, ?_, ?_, by simp [c]⟩
          · intro v hv
            rw [hUeq] at hv
            rcases Finset.mem_insert.mp hv with rfl | hv'
            · simp [c, Forb, hfr]
            · rcases Finset.mem_insert.mp hv' with rfl | hv''
              · simp only [c, hur, if_false, if_true, Forb]
                cases hf : f v with
                | none => simp
                | some b => simp [hcu b hf]
              · rw [Finset.mem_singleton.mp hv'']
                simp only [c, hwr, huw.symm, if_false, Forb]
                cases hf : f w with
                | none => simp
                | some b => simp [hcw b hf]
          · intro x hx y hy hadj
            rw [hUeq] at hx hy
            rcases Finset.mem_insert.mp hx with rfl | hx' <;> rcases Finset.mem_insert.mp hy with rfl | hy'
            · exact (G.ne_of_adj hadj rfl).elim
            · rcases Finset.mem_insert.mp hy' with rfl | hy''
              · simp [c, hur, Ne.symm hcua]
              · rw [Finset.mem_singleton.mp hy'']; simp [c, hwr, huw.symm, Ne.symm hcwa]
            · rcases Finset.mem_insert.mp hx' with rfl | hx''
              · simp [c, hur, hcua]
              · rw [Finset.mem_singleton.mp hx'']; simp [c, hwr, huw.symm, hcwa]
            · rcases Finset.mem_insert.mp hx' with rfl | hx'' <;> rcases Finset.mem_insert.mp hy' with rfl | hy''
              · exact (G.ne_of_adj hadj rfl).elim
              · rw [Finset.mem_singleton.mp hy'']; simp [c, hur, hwr, huw.symm, hcuw]
              · rw [Finset.mem_singleton.mp hx'']; simp [c, hur, hwr, huw.symm, Ne.symm hcuw]
              · rw [Finset.mem_singleton.mp hx'', Finset.mem_singleton.mp hy''] at hadj
                exact (G.ne_of_adj hadj rfl).elim
      rw [h1, triangle_forb_char]
      apply not_congr
      constructor
      · rintro ⟨b, hba, hfu, hfw⟩
        exact ⟨b, hba, fun v hv => by rcases Finset.mem_insert.mp hv with rfl | hv'; exact hfu; rw [Finset.mem_singleton.mp hv']; exact hfw⟩
      · rintro ⟨b, hba, hall⟩
        exact ⟨b, hba, hall u (by simp), hall w (by simp)⟩

end DeficitChar

section TwoDeficitAndMain

variable {V : Type*} [DecidableEq V] [Fintype V]

def LOfCons {k : Nat} (C : V → List (Finset (Fin k))) (x : Fin k → Fin 3) (v : V) : Finset (Fin 3) :=
  Finset.univ.filter (fun c => ∀ s ∈ C v, ¬ ∀ i ∈ s, x i = c)

def unionList {k : Nat} : List (Finset (Fin k)) → Finset (Fin k)
  | [] => ∅
  | s :: rest => s ∪ unionList rest

lemma mem_unionList {k : Nat} (l : List (Finset (Fin k))) (i : Fin k) :
    i ∈ unionList l ↔ ∃ s ∈ l, i ∈ s := by
  induction l with
  | nil => simp [unionList]
  | cons a rest ih => simp [unionList, ih]

noncomputable def monoColor {k : Nat} (P : Finset (Fin k)) (x : Fin k → Fin 3) : Option (Fin 3) := by
  classical
  exact if h : ∃ b : Fin 3, ∀ i ∈ P, x i = b then some (Classical.choose h) else none

lemma monoColor_eq_some_iff {k : Nat} {P : Finset (Fin k)} (hP : P.Nonempty) (x : Fin k → Fin 3) (c : Fin 3) :
    monoColor P x = some c ↔ ∀ i ∈ P, x i = c := by
  classical
  unfold monoColor
  split_ifs with h
  · constructor
    · intro heq
      have hc : Classical.choose h = c := Option.some.inj heq
      rw [← hc]
      exact Classical.choose_spec h
    · intro hall
      congr 1
      obtain ⟨i0, hi0⟩ := hP
      have h1 := Classical.choose_spec h i0 hi0
      have h2 := hall i0 hi0
      rw [← h1, h2]
  · constructor
    · intro heq; exact absurd heq (by simp)
    · intro hall; exact (h ⟨c, hall⟩).elim

lemma opt3_char (o0 o1 o2 : Option (Fin 3)) :
    (∃ c : Fin 3, o0 ≠ some c ∧ o1 ≠ some c ∧ o2 ≠ some c) ↔
    ¬ ∃ p : Equiv.Perm (Fin 3), o0 = some (p 0) ∧ o1 = some (p 1) ∧ o2 = some (p 2) := by
  cases o0 with
  | none =>
    constructor
    · intro _ ⟨p, h0, _, _⟩; cases h0
    · intro _
      cases o1 with
      | none =>
        cases o2 with
        | none => exact ⟨0, by simp, by simp, by simp⟩
        | some a2 => fin_cases a2 <;> decide
      | some a1 =>
        fin_cases a1 <;> cases o2 with
        | none => decide
        | some a2 => fin_cases a2 <;> decide
  | some a0 =>
    cases o1 with
    | none =>
      constructor
      · intro _ ⟨p, _, h1, _⟩; cases h1
      · intro _
        fin_cases a0 <;> cases o2 with
        | none => decide
        | some a2 => fin_cases a2 <;> decide
    | some a1 =>
      cases o2 with
      | none =>
        constructor
        · intro _ ⟨p, _, _, h2⟩; cases h2
        · intro _
          fin_cases a0 <;> fin_cases a1 <;> decide
      | some a2 =>
        constructor
        · rintro ⟨c, h0, h1, h2⟩ ⟨p, hp0, hp1, hp2⟩
          have ha0 : a0 = p 0 := Option.some.inj hp0
          have ha1 : a1 = p 1 := Option.some.inj hp1
          have ha2 : a2 = p 2 := Option.some.inj hp2
          have hc : p.symm c = 0 ∨ p.symm c = 1 ∨ p.symm c = 2 := by
            have hall3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
            exact hall3 (p.symm c)
          rcases hc with h | h | h
          · apply h0; congr 1; rw [ha0, ← h, p.apply_symm_apply]
          · apply h1; congr 1; rw [ha1, ← h, p.apply_symm_apply]
          · apply h2; congr 1; rw [ha2, ← h, p.apply_symm_apply]
        · intro hnot
          by_cases h01 : a0 = a1
          · subst h01
            have : ∃ c : Fin 3, some a0 ≠ some c ∧ some a2 ≠ some c := by
              fin_cases a0 <;> fin_cases a2 <;> decide
            obtain ⟨c, hc0, hc2⟩ := this
            exact ⟨c, hc0, hc0, hc2⟩
          · by_cases h02 : a0 = a2
            · subst h02
              have : ∃ c : Fin 3, some a0 ≠ some c ∧ some a1 ≠ some c := by
                fin_cases a0 <;> fin_cases a1 <;> decide
              obtain ⟨c, hc0, hc1⟩ := this
              exact ⟨c, hc0, hc1, hc0⟩
            · by_cases h12 : a1 = a2
              · subst h12
                have : ∃ c : Fin 3, some a0 ≠ some c ∧ some a1 ≠ some c := by
                  fin_cases a0 <;> fin_cases a1 <;> decide
                obtain ⟨c, hc0, hc1⟩ := this
                exact ⟨c, hc0, hc1, hc1⟩
              · exfalso
                apply hnot
                let f : Fin 3 → Fin 3 := fun i => if i = 0 then a0 else if i = 1 then a1 else a2
                have hinj : Function.Injective f := by
                  intro i j hij
                  fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢
                  · exact (h01 hij).elim
                  · exact (h02 hij).elim
                  · exact (h01 hij.symm).elim
                  · exact (h12 hij).elim
                  · exact (h02 hij.symm).elim
                  · exact (h12 hij.symm).elim
                exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj),
                  by simp [f], by simp [f], by simp [f]⟩

lemma single_vertex_cons_char {k : Nat} (P0 P1 P2 : Finset (Fin k))
    (h0 : P0.Nonempty) (h1 : P1.Nonempty) (h2 : P2.Nonempty) (x : Fin k → Fin 3) :
    (∃ c : Fin 3, (¬ ∀ i ∈ P0, x i = c) ∧ (¬ ∀ i ∈ P1, x i = c) ∧ (¬ ∀ i ∈ P2, x i = c)) ↔
    ¬ ∃ p : Equiv.Perm (Fin 3), (∀ i ∈ P0, x i = p 0) ∧ (∀ i ∈ P1, x i = p 1) ∧ (∀ i ∈ P2, x i = p 2) := by
  have hL : (∃ c : Fin 3, (¬ ∀ i ∈ P0, x i = c) ∧ (¬ ∀ i ∈ P1, x i = c) ∧ (¬ ∀ i ∈ P2, x i = c)) ↔
      (∃ c : Fin 3, monoColor P0 x ≠ some c ∧ monoColor P1 x ≠ some c ∧ monoColor P2 x ≠ some c) := by
    apply exists_congr
    intro c
    simp only [ne_eq, monoColor_eq_some_iff h0, monoColor_eq_some_iff h1, monoColor_eq_some_iff h2]
  have hR : (∃ p : Equiv.Perm (Fin 3), (∀ i ∈ P0, x i = p 0) ∧ (∀ i ∈ P1, x i = p 1) ∧ (∀ i ∈ P2, x i = p 2)) ↔
      (∃ p : Equiv.Perm (Fin 3), monoColor P0 x = some (p 0) ∧ monoColor P1 x = some (p 1) ∧ monoColor P2 x = some (p 2)) := by
    apply exists_congr
    intro p
    simp only [monoColor_eq_some_iff h0, monoColor_eq_some_iff h1, monoColor_eq_some_iff h2]
  rw [hL, hR]
  exact opt3_char (monoColor P0 x) (monoColor P1 x) (monoColor P2 x)

lemma two_deficit_char {G : SimpleGraph V} [DecidableRel G.Adj] {k : Nat} :
    ∀ n : Nat, ∀ U : Finset V, U.card = n → U.Nonempty → ConnIn G U →
      (∀ v ∈ U, degIn G U v ≤ 3) →
      ¬ (U.card = 4 ∧ ∀ v ∈ U, degIn G U v = 3) →
      Uncolorable G U → 3 * (pCount G U - 2) = U.card + 2 →
      ∀ (C : V → List (Finset (Fin k))),
        (∀ v ∈ U, (C v).length = 3 - degIn G U v) →
        (∀ v ∈ U, ∀ s ∈ C v, s.Nonempty) →
        ∃ P : Fin 3 → Finset (Fin k),
          (∀ m : Fin 3, (P m).Nonempty) ∧
          (Finset.univ.biUnion P = U.biUnion (fun v => unionList (C v))) ∧
          ∀ x : Fin k → Fin 3, Colorable G U (LOfCons C x) ↔
            ¬ ∃ p : Equiv.Perm (Fin 3), ∀ m : Fin 3, ∀ i ∈ P m, x i = p m := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro U hcard hne hconn hmax hnk4 hunc hdef C hlen hCne
    classical
    by_cases hcut : ∃ y ∈ U, ¬ ConnIn G (U.erase y)
    · obtain ⟨y0, hy0, hnot⟩ := hcut
      obtain ⟨A0, B0, z0, hs0⟩ := has_bridge_of_cut hconn hmax hy0 hnot
      obtain ⟨L0, hdeg0, hnc0⟩ := hunc
      obtain ⟨huncA0, huncB0⟩ := bridge_split_uncolorable hs0 hdeg0 hnc0
      have hA0_sub : A0 ⊆ U := by rw [← hs0.1]; exact Finset.subset_union_left
      have hB0_sub : B0 ⊆ U := by rw [← hs0.1]; exact Finset.subset_union_right
      have hcard0 : A0.card + B0.card = U.card := by rw [← hs0.1, Finset.card_union_of_disjoint hs0.2.1]
      have hmaxA0 : ∀ v ∈ A0, degIn G A0 v ≤ 3 := fun v hv => le_trans (degIn_mono hA0_sub v) (hmax v (hA0_sub hv))
      have hmaxB0 : ∀ v ∈ B0, degIn G B0 v ≤ 3 := fun v hv => le_trans (degIn_mono hB0_sub v) (hmax v (hB0_sub hv))
      have hnk4A0 : ¬ (A0.card = 4 ∧ ∀ v ∈ A0, degIn G A0 v = 3) := by
        rintro ⟨_, hall⟩; have hd := degIn_bridge_left hs0 y0 hs0.2.2.2.2.1; have hm := hmax y0 (hA0_sub hs0.2.2.2.2.1)
        have h3 := hall y0 hs0.2.2.2.2.1; simp at hd; omega
      have hnk4B0 : ¬ (B0.card = 4 ∧ ∀ v ∈ B0, degIn G B0 v = 3) := by
        rintro ⟨_, hall⟩; have hd := degIn_bridge_left (bridge_split_symm hs0) z0 hs0.2.2.2.2.2.1; have hm := hmax z0 (hB0_sub hs0.2.2.2.2.2.1)
        have h3 := hall z0 hs0.2.2.2.2.2.1; simp at hd; omega
      obtain ⟨hpA0, hleA0, ⟨mA0, hmA0⟩⟩ := uncolorable_deficit A0.card A0 rfl ⟨y0, hs0.2.2.2.2.1⟩ hs0.2.2.1 hmaxA0 hnk4A0 huncA0
      obtain ⟨hpB0, hleB0, ⟨mB0, hmB0⟩⟩ := uncolorable_deficit B0.card B0 rfl ⟨z0, hs0.2.2.2.2.2.1⟩ hs0.2.2.2.1 hmaxB0 hnk4B0 huncB0
      have hp0 := pCount_bridge_split hs0 hmax
      have hsplit : ∃ A B y z, IsBridgeSplit G U A B y z ∧
          Uncolorable G A ∧ Uncolorable G B ∧
          3 * (pCount G A - 2) = A.card ∧ 3 * (pCount G B - 2) = B.card + 2 := by
        by_cases h0 : mA0 = 0
        · exact ⟨A0, B0, y0, z0, hs0, huncA0, huncB0, by omega, by omega⟩
        · exact ⟨B0, A0, z0, y0, bridge_split_symm hs0, huncB0, huncA0, by omega, by omega⟩
      obtain ⟨A, B, y, z, hs, huncA, huncB, hdefA, hdefB⟩ := hsplit
      have hA_sub : A ⊆ U := by rw [← hs.1]; exact Finset.subset_union_left
      have hB_sub : B ⊆ U := by rw [← hs.1]; exact Finset.subset_union_right
      have hcardAB : A.card + B.card = U.card := by rw [← hs.1, Finset.card_union_of_disjoint hs.2.1]
      have hA_ne : A.Nonempty := ⟨y, hs.2.2.2.2.1⟩
      have hB_ne : B.Nonempty := ⟨z, hs.2.2.2.2.2.1⟩
      have hB_lt : B.card < n := by have := Finset.card_pos.mpr hA_ne; omega
      have hmaxA : ∀ v ∈ A, degIn G A v ≤ 3 := fun v hv => le_trans (degIn_mono hA_sub v) (hmax v (hA_sub hv))
      have hmaxB : ∀ v ∈ B, degIn G B v ≤ 3 := fun v hv => le_trans (degIn_mono hB_sub v) (hmax v (hB_sub hv))
      have hnk4A : ¬ (A.card = 4 ∧ ∀ v ∈ A, degIn G A v = 3) := by
        rintro ⟨_, hall⟩; have hd := degIn_bridge_left hs y hs.2.2.2.2.1; have hm := hmax y (hA_sub hs.2.2.2.2.1)
        have h3 := hall y hs.2.2.2.2.1; simp at hd; omega
      have hnk4B : ¬ (B.card = 4 ∧ ∀ v ∈ B, degIn G B v = 3) := by
        rintro ⟨_, hall⟩; have hd := degIn_bridge_left (bridge_split_symm hs) z hs.2.2.2.2.2.1; have hm := hmax z (hB_sub hs.2.2.2.2.2.1)
        have h3 := hall z hs.2.2.2.2.2.1; simp at hd; omega
      have hgeA := zero_deficit_deg_ge_two A.card A rfl hA_ne hs.2.2.1 hmaxA hnk4A huncA hdefA
      have hdyU := degIn_bridge_left hs y hs.2.2.2.2.1
      have hdzU := degIn_bridge_left (bridge_split_symm hs) z hs.2.2.2.2.2.1
      have hdyA : degIn G A y = 2 := by
        have h1 := hgeA y hs.2.2.2.2.1; have h2 := hmax y (hA_sub hs.2.2.2.2.1); simp at hdyU; omega
      obtain ⟨hTA_ne, hcharA⟩ := zero_deficit_char A.card A rfl hA_ne hs.2.2.1 hmaxA hnk4A huncA hdefA y hs.2.2.2.2.1 hdyA
      let TA := A.filter (fun v => v ≠ y ∧ degIn G A v = 2)
      let sA : Finset (Fin k) := A.biUnion (fun v => unionList (C v))
      have hsA_ne : sA.Nonempty := by
        obtain ⟨v0, hv0⟩ := hTA_ne
        have ⟨hv0A, hv0y, hdv0A⟩ := Finset.mem_filter.mp hv0
        have hdU := degIn_bridge_left hs v0 hv0A
        simp [hv0y] at hdU
        have hlen0 : (C v0).length = 1 := by have := hlen v0 (hA_sub hv0A); omega
        obtain ⟨s0, hs0eq⟩ := List.length_eq_one_iff.mp hlen0
        have hs0ne : s0.Nonempty := hCne v0 (hA_sub hv0A) s0 (by rw [hs0eq]; simp)
        obtain ⟨i0, hi0⟩ := hs0ne
        refine ⟨i0, Finset.mem_biUnion.mpr ⟨v0, hv0A, ?_⟩⟩
        rw [hs0eq]; simp [unionList, hi0]
      let C' : V → List (Finset (Fin k)) := fun v => if v = z then sA :: C v else C v
      have hlen' : ∀ v ∈ B, (C' v).length = 3 - degIn G B v := by
        intro v hv
        have hdU := degIn_bridge_left (bridge_split_symm hs) v hv
        have hm := hmax v (hB_sub hv)
        have hl := hlen v (hB_sub hv)
        by_cases hvz : v = z
        · subst hvz; simp only [C', if_true, List.length_cons]; simp at hdU; omega
        · simp only [C', hvz, if_false]; simp [hvz] at hdU; omega
      have hCne' : ∀ v ∈ B, ∀ s ∈ C' v, s.Nonempty := by
        intro v hv s hsMem
        by_cases hvz : v = z
        · subst hvz
          simp only [C', if_true, List.mem_cons] at hsMem
          rcases hsMem with rfl | hmem
          · exact hsA_ne
          · exact hCne v (hB_sub hv) s hmem
        · simp only [C', hvz, if_false] at hsMem
          exact hCne v (hB_sub hv) s hsMem
      obtain ⟨P, hPne, hPunion, hPchar⟩ := ih B.card hB_lt B rfl hB_ne hs.2.2.2.1 hmaxB hnk4B huncB hdefB C' hlen' hCne'
      refine ⟨P, hPne, ?_, ?_⟩
      · rw [hPunion]
        ext i
        simp only [Finset.mem_biUnion]
        constructor
        · rintro ⟨v, hvB, hi⟩
          by_cases hvz : v = z
          · subst hvz
            simp only [C', if_true, unionList, Finset.mem_union] at hi
            rcases hi with hisA | hiv
            · obtain ⟨w, hwA, hiw⟩ := Finset.mem_biUnion.mp hisA
              exact ⟨w, hA_sub hwA, hiw⟩
            · exact ⟨v, hB_sub hvB, hiv⟩
          · simp only [C', hvz, if_false] at hi
            exact ⟨v, hB_sub hvB, hi⟩
        · rintro ⟨v, hvU, hi⟩
          rw [← hs.1] at hvU
          rcases Finset.mem_union.mp hvU with hvA | hvB
          · refine ⟨z, hs.2.2.2.2.2.1, ?_⟩
            simp only [C', if_true, unionList, Finset.mem_union]
            exact Or.inl (Finset.mem_biUnion.mpr ⟨v, hvA, hi⟩)
          · refine ⟨v, hvB, ?_⟩
            by_cases hvz : v = z
            · subst hvz; simp [C', unionList, hi]
            · simp [C', hvz, hi]
      · intro x
        rw [← hPchar x]
        let fx : V → Option (Fin 3) := fun v =>
          match C v with
          | [s] => monoColor s x
          | _ => none
        have hL_eq_A : ∀ v ∈ A, LOfCons C x v = Forb fx v := by
          intro v hvA
          have hdvA := hgeA v hvA
          have hdU := degIn_bridge_left hs v hvA
          have hm := hmax v (hA_sub hvA)
          have hl := hlen v (hA_sub hvA)
          by_cases hvy : v = y
          · subst hvy
            have hl0 : (C v).length = 0 := by simp at hdU; omega
            have hC0 : C v = [] := List.eq_nil_of_length_eq_zero hl0
            ext c; simp [LOfCons, Forb, fx, hC0]
          · by_cases hd3 : degIn G A v = 3
            · have hl0 : (C v).length = 0 := by simp [hvy] at hdU; omega
              have hC0 : C v = [] := List.eq_nil_of_length_eq_zero hl0
              ext c; simp [LOfCons, Forb, fx, hC0]
            · have hl1 : (C v).length = 1 := by simp [hvy] at hdU; omega
              obtain ⟨s, hCs⟩ := List.length_eq_one_iff.mp hl1
              have hsne : s.Nonempty := hCne v (hA_sub hvA) s (by rw [hCs]; simp)
              ext c
              simp only [LOfCons, Finset.mem_filter, Finset.mem_univ, true_and, hCs, List.mem_singleton, forall_eq, Forb, fx]
              cases hmC : monoColor s x with
              | none =>
                simp only [Finset.mem_univ, iff_true]
                intro hall
                have := (monoColor_eq_some_iff hsne x c).mpr hall
                rw [hmC] at this; cases this
              | some b =>
                simp only [Finset.mem_erase, Finset.mem_univ, and_true]
                constructor
                · intro hnot heq
                  subst heq
                  exact hnot ((monoColor_eq_some_iff hsne x c).mp hmC)
                · intro hne hall
                  have := (monoColor_eq_some_iff hsne x c).mpr hall
                  rw [hmC] at this
                  exact hne (Option.some.inj this).symm
        have hfy : fx y = none := by
          have hl0 : (C y).length = 0 := by have := hlen y (hA_sub hs.2.2.2.2.1); simp at hdyU; omega
          simp [fx, List.eq_nil_of_length_eq_zero hl0]
        have hf3A : ∀ v ∈ A, degIn G A v = 3 → fx v = none := by
          intro v hvA hd3
          have hdU := degIn_bridge_left hs v hvA
          have hm := hmax v (hA_sub hvA)
          have hl0 : (C v).length = 0 := by have := hlen v (hA_sub hvA); omega
          simp [fx, List.eq_nil_of_length_eq_zero hl0]
        have hall_sA : ∀ b : Fin 3, (∀ v ∈ TA, fx v = some b) ↔ (∀ i ∈ sA, x i = b) := by
          intro b
          constructor
          · intro hall i hi
            obtain ⟨v, hvA, hiv⟩ := Finset.mem_biUnion.mp hi
            have hdvA := hgeA v hvA
            have hdU := degIn_bridge_left hs v hvA
            have hm := hmax v (hA_sub hvA)
            have hl := hlen v (hA_sub hvA)
            by_cases hvy : v = y
            · subst hvy
              have hl0 : (C v).length = 0 := by simp at hdU; omega
              rw [List.eq_nil_of_length_eq_zero hl0] at hiv
              simp [unionList] at hiv
            · by_cases hd3 : degIn G A v = 3
              · have hl0 : (C v).length = 0 := by simp [hvy] at hdU; omega
                rw [List.eq_nil_of_length_eq_zero hl0] at hiv
                simp [unionList] at hiv
              · have hdv2 : degIn G A v = 2 := by omega
                have hl1 : (C v).length = 1 := by simp [hvy] at hdU; omega
                obtain ⟨s, hCs⟩ := List.length_eq_one_iff.mp hl1
                have hsne : s.Nonempty := hCne v (hA_sub hvA) s (by rw [hCs]; simp)
                have his : i ∈ s := by rw [hCs] at hiv; simpa [unionList] using hiv
                have hfv := hall v (Finset.mem_filter.mpr ⟨hvA, hvy, hdv2⟩)
                simp only [fx, hCs] at hfv
                exact (monoColor_eq_some_iff hsne x b).mp hfv i his
          · intro hall v hvTA
            have ⟨hvA, hvy, hdvA⟩ := Finset.mem_filter.mp hvTA
            have hdU := degIn_bridge_left hs v hvA
            have hl1 : (C v).length = 1 := by have := hlen v (hA_sub hvA); simp [hvy] at hdU; omega
            obtain ⟨s, hCs⟩ := List.length_eq_one_iff.mp hl1
            have hsne : s.Nonempty := hCne v (hA_sub hvA) s (by rw [hCs]; simp)
            simp only [fx, hCs]
            apply (monoColor_eq_some_iff hsne x b).mpr
            intro i his
            exact hall i (Finset.mem_biUnion.mpr ⟨v, hvA, by rw [hCs]; simp [unionList, his]⟩)
        constructor
        · rintro ⟨c, hcL, hcadj⟩
          refine ⟨c, ?_, fun u hu v hv ha => hcadj u (hB_sub hu) v (hB_sub hv) ha⟩
          intro v hvB
          by_cases hvz : v = z
          · subst hvz
            simp only [LOfCons, C', if_true, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons]
            intro s hsMem
            rcases hsMem with rfl | hmem
            · intro hall
              have hAok := (hcharA fx hfy hf3A (c y)).mp ⟨c, fun w hw => by rw [← hL_eq_A w hw]; exact hcL w (hA_sub hw),
                fun u hu w hw ha => hcadj u (hA_sub hu) w (hA_sub hw) ha, rfl⟩
              have hne : c v ≠ c y := hcadj v (hB_sub hvB) y (hA_sub hs.2.2.2.2.1) hs.2.2.2.2.2.2.1.symm
              exact hAok ⟨c v, hne, (hall_sA (c v)).mpr hall⟩
            · have hm := hcL v (hB_sub hvB)
              simp only [LOfCons, Finset.mem_filter, Finset.mem_univ, true_and] at hm
              exact hm s hmem
          · have hm := hcL v (hB_sub hvB)
            simpa [LOfCons, C', hvz] using hm
        · rintro ⟨cB, hcBL, hcBadj⟩
          have hz_ok : ¬ ∀ i ∈ sA, x i = cB z := by
            have hm := hcBL z hs.2.2.2.2.2.1
            simp only [LOfCons, C', if_true, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons] at hm
            exact hm sA (Or.inl rfl)
          have hA_col : ∃ cA : V → Fin 3, (∀ v ∈ A, cA v ∈ Forb fx v) ∧
              (∀ u ∈ A, ∀ v ∈ A, G.Adj u v → cA u ≠ cA v) ∧ cA y ≠ cB z := by
            by_cases hex : ∃ b : Fin 3, ∀ i ∈ sA, x i = b
            · obtain ⟨b, hb⟩ := hex
              have hne : b ≠ cB z := fun heq => hz_ok (heq ▸ hb)
              have hexA : ∃ cA : V → Fin 3, (∀ v ∈ A, cA v ∈ Forb fx v) ∧
                  (∀ u ∈ A, ∀ v ∈ A, G.Adj u v → cA u ≠ cA v) ∧ cA y = b := by
                rw [hcharA fx hfy hf3A b]
                rintro ⟨b', hb'ne, hall'⟩
                obtain ⟨i0, hi0⟩ := hsA_ne
                have h1 := hb i0 hi0
                have h2 := (hall_sA b').mp hall' i0 hi0
                exact hb'ne (h2.symm.trans h1)
              obtain ⟨cA, h1, h2, h3⟩ := hexA
              exact ⟨cA, h1, h2, by rw [h3]; exact hne⟩
            · obtain ⟨cy, hcy⟩ : ∃ cy : Fin 3, cy ≠ cB z := by
                have hall3 : ∀ k : Fin 3, ∃ cy : Fin 3, cy ≠ k := by decide
                exact hall3 (cB z)
              have hexA : ∃ cA : V → Fin 3, (∀ v ∈ A, cA v ∈ Forb fx v) ∧
                  (∀ u ∈ A, ∀ v ∈ A, G.Adj u v → cA u ≠ cA v) ∧ cA y = cy := by
                rw [hcharA fx hfy hf3A cy]
                rintro ⟨b', _, hall'⟩
                exact hex ⟨b', (hall_sA b').mp hall'⟩
              obtain ⟨cA, h1, h2, h3⟩ := hexA
              exact ⟨cA, h1, h2, by rw [h3]; exact hcy⟩
          obtain ⟨cA, hcAL, hcAadj, hcyne⟩ := hA_col
          refine ⟨fun v => if v ∈ A then cA v else cB v, ?_, ?_⟩
          · intro v hv
            rw [← hs.1] at hv
            by_cases hvA : v ∈ A
            · simp only [hvA, if_true]
              rw [hL_eq_A v hvA]
              exact hcAL v hvA
            · have hvB : v ∈ B := (Finset.mem_union.mp hv).resolve_left hvA
              simp only [hvA, if_false]
              have hm := hcBL v hvB
              by_cases hvz : v = z
              · subst hvz
                simp only [LOfCons, C', if_true, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons] at hm ⊢
                exact fun s hmem => hm s (Or.inr hmem)
              · simpa [LOfCons, C', hvz] using hm
          · intro u hu v hv hadj
            rw [← hs.1] at hu hv
            by_cases huA : u ∈ A <;> by_cases hvA : v ∈ A
            · simp [huA, hvA, hcAadj u huA v hvA hadj]
            · have hvB : v ∈ B := (Finset.mem_union.mp hv).resolve_left hvA
              have ⟨huy, hvz⟩ := hs.2.2.2.2.2.2.2 u huA v hvB hadj
              subst huy; subst hvz; simp [huA, hvA, hcyne]
            · have huB : u ∈ B := (Finset.mem_union.mp hu).resolve_left huA
              have ⟨hvy, huz⟩ := hs.2.2.2.2.2.2.2 v hvA u huB hadj.symm
              subst hvy; subst huz; simp [huA, hvA, Ne.symm hcyne]
            · have huB : u ∈ B := (Finset.mem_union.mp hu).resolve_left huA
              have hvB : v ∈ B := (Finset.mem_union.mp hv).resolve_left hvA
              simp [huA, hvA, hcBadj u huB v hvB hadj]
    · push_neg at hcut
      have hc1 : U.card = 1 := by
        by_contra hne1
        by_cases hc2 : U.card = 2
        · obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hc2
          have hadj : G.Adj u v := by
            have hr := hconn u (by simp) v (by simp)
            rcases Relation.ReflTransGen.cases_head hr with h | ⟨w, huw, _⟩
            · exact absurd h huv
            · rcases Finset.mem_insert.mp huw.2.1 with rfl | hw
              · exact (G.ne_of_adj huw.2.2 rfl).elim
              · rw [Finset.mem_singleton.mp hw] at huw; exact huw.2.2
          have hdu : degIn G {u, v} u = 1 := by
            unfold degIn
            have : ({u, v} : Finset V).filter (fun w => G.Adj u w) = {v} := by
              ext w; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨rfl | rfl, ha⟩
                · exact (G.ne_of_adj ha rfl).elim
                · rfl
              · rintro rfl; exact ⟨Or.inr rfl, hadj⟩
            rw [this, Finset.card_singleton]
          have hdv : degIn G {u, v} v = 1 := by
            unfold degIn
            have : ({u, v} : Finset V).filter (fun w => G.Adj v w) = {u} := by
              ext w; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨rfl | rfl, ha⟩
                · rfl
                · exact (G.ne_of_adj ha rfl).elim
              · rintro rfl; exact ⟨Or.inl rfl, hadj.symm⟩
            rw [this, Finset.card_singleton]
          have hp : pCount G {u, v} = 4 := by simp [pCount, Finset.sum_pair huv, hdu, hdv]
          have hc2' : ({u, v} : Finset V).card = 2 := Finset.card_pair huv
          rw [hp, hc2'] at hdef; omega
        · have hc3 : 3 ≤ U.card := by have := Finset.card_pos.mpr hne; omega
          obtain ⟨L, hdeg, hnc⟩ := hunc
          obtain ⟨h2reg, ⟨m, hm⟩⟩ := two_conn_gallai hconn hc3 hmax hnk4 hcut hdeg hnc
          have hp : pCount G U = U.card := by
            unfold pCount
            calc U.sum (fun v => 3 - degIn G U v) = U.sum (fun _ => 1) := by
                  apply Finset.sum_congr rfl; intro v hv; rw [h2reg v hv]
              _ = U.card := by simp
          rw [hp] at hdef
          omega
      obtain ⟨v0, rfl⟩ := Finset.card_eq_one.mp hc1
      have hd0 : degIn G {v0} v0 = 0 := by
        unfold degIn
        have : ({v0} : Finset V).filter (fun w => G.Adj v0 w) = ∅ := by
          ext w; simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
          rintro rfl ha; exact G.ne_of_adj ha rfl
        rw [this, Finset.card_empty]
      have hlen3 : (C v0).length = 3 := by have := hlen v0 (by simp); rw [hd0] at this; omega
      rcases hCeq : C v0 with _ | ⟨P0, _ | ⟨P1, _ | ⟨P2, _ | _⟩⟩⟩ <;> simp [hCeq] at hlen3
      have hP0 : P0.Nonempty := hCne v0 (by simp) P0 (by rw [hCeq]; simp)
      have hP1 : P1.Nonempty := hCne v0 (by simp) P1 (by rw [hCeq]; simp)
      have hP2 : P2.Nonempty := hCne v0 (by simp) P2 (by rw [hCeq]; simp)
      let P : Fin 3 → Finset (Fin k) := fun m => if m = 0 then P0 else if m = 1 then P1 else P2
      refine ⟨P, ?_, ?_, ?_⟩
      · intro m; fin_cases m <;> simp [P, hP0, hP1, hP2]
      · ext i
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_singleton, exists_eq_left,
          hCeq, unionList, Finset.mem_union, Finset.notMem_empty, or_false]
        constructor
        · rintro ⟨m, hm⟩; fin_cases m <;> simp [P] at hm <;> tauto
        · rintro (h | h | h)
          · exact ⟨0, by simp [P, h]⟩
          · exact ⟨1, by simp [P, h]⟩
          · exact ⟨2, by simp [P, h]⟩
      · intro x
        have hcol : Colorable G {v0} (LOfCons C x) ↔
            ∃ c : Fin 3, (¬ ∀ i ∈ P0, x i = c) ∧ (¬ ∀ i ∈ P1, x i = c) ∧ (¬ ∀ i ∈ P2, x i = c) := by
          constructor
          · rintro ⟨c, hcL, _⟩
            have hm := hcL v0 (by simp)
            simp only [LOfCons, hCeq, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons, List.not_mem_nil, or_false] at hm
            exact ⟨c v0, hm P0 (Or.inl rfl), hm P1 (Or.inr (Or.inl rfl)), hm P2 (Or.inr (Or.inr rfl))⟩
          · rintro ⟨c, h0, h1, h2⟩
            refine ⟨fun _ => c, ?_, ?_⟩
            · intro v hv
              rw [Finset.mem_singleton.mp hv]
              simp only [LOfCons, hCeq, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons, List.not_mem_nil, or_false]
              rintro s (rfl | rfl | rfl)
              · exact h0
              · exact h1
              · exact h2
            · intro a ha b hb hab
              rw [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb] at hab
              exact (G.ne_of_adj hab rfl).elim
        rw [hcol, single_vertex_cons_char P0 P1 P2 hP0 hP1 hP2 x]
        apply not_congr
        apply exists_congr
        intro p
        constructor
        · intro ⟨hp0, hp1, hp2⟩ m
          fin_cases m
          · exact hp0
          · exact hp1
          · exact hp2
        · intro hall
          exact ⟨by simpa [P] using hall 0, by simpa [P] using hall 1, by simpa [P] using hall 2⟩

end TwoDeficitAndMain

section ZeroDeficitWholeAndMain

variable {V : Type*} [DecidableEq V] [Fintype V]

lemma opt2_neq_char (oA oB : Option (Fin 3)) :
    (∃ a b : Fin 3, a ≠ b ∧ (oA = none ∨ oA = some a) ∧ (oB = none ∨ oB = some b)) ↔
    ¬ ∃ c : Fin 3, oA = some c ∧ oB = some c := by
  cases oA with
  | none =>
    cases oB with
    | none => decide
    | some b0 => fin_cases b0 <;> decide
  | some a0 =>
    fin_cases a0 <;> cases oB with
    | none => decide
    | some b0 => fin_cases b0 <;> decide

lemma zero_deficit_whole {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V}
    (hne : U.Nonempty) (hconn : ConnIn G U)
    (hmax : ∀ v ∈ U, degIn G U v ≤ 3)
    (hnk4 : ¬ (U.card = 4 ∧ ∀ v ∈ U, degIn G U v = 3))
    (hunc : Uncolorable G U) (hdef : 3 * (pCount G U - 2) = U.card)
    (hp5 : 5 ≤ pCount G U) :
    let T := U.filter (fun v => degIn G U v = 2)
    T.Nonempty ∧
    ∀ (f : V → Option (Fin 3)), (∀ v ∈ U, degIn G U v = 3 → f v = none) →
      (Colorable G U (Forb f) ↔ ¬ ∃ b : Fin 3, ∀ v ∈ T, f v = some b) := by
  classical
  dsimp only
  have hcut : ∃ y ∈ U, ¬ ConnIn G (U.erase y) := by
    by_contra hnc
    push_neg at hnc
    have hc3 : 3 ≤ U.card := by omega
    obtain ⟨L, hdeg, hncL⟩ := hunc
    obtain ⟨h2reg, _⟩ := two_conn_gallai hconn hc3 hmax hnk4 hnc hdeg hncL
    have hpU : pCount G U = U.card := by
      unfold pCount
      calc U.sum (fun v => 3 - degIn G U v) = U.sum (fun _ => 1) := by
            apply Finset.sum_congr rfl; intro v hv; rw [h2reg v hv]
        _ = U.card := by simp
    omega
  obtain ⟨y, hy, hnot⟩ := hcut
  obtain ⟨A, B, z, hs⟩ := has_bridge_of_cut hconn hmax hy hnot
  obtain ⟨L, hdeg, hnc⟩ := hunc
  obtain ⟨huncA, huncB⟩ := bridge_split_uncolorable hs hdeg hnc
  have hA_sub : A ⊆ U := by rw [← hs.1]; exact Finset.subset_union_left
  have hB_sub : B ⊆ U := by rw [← hs.1]; exact Finset.subset_union_right
  have hcardAB : A.card + B.card = U.card := by rw [← hs.1, Finset.card_union_of_disjoint hs.2.1]
  have hA_ne : A.Nonempty := ⟨y, hs.2.2.2.2.1⟩
  have hB_ne : B.Nonempty := ⟨z, hs.2.2.2.2.2.1⟩
  have hmaxA : ∀ v ∈ A, degIn G A v ≤ 3 := fun v hv => le_trans (degIn_mono hA_sub v) (hmax v (hA_sub hv))
  have hmaxB : ∀ v ∈ B, degIn G B v ≤ 3 := fun v hv => le_trans (degIn_mono hB_sub v) (hmax v (hB_sub hv))
  have hnk4A : ¬ (A.card = 4 ∧ ∀ v ∈ A, degIn G A v = 3) := by
    rintro ⟨_, hall⟩
    have hdy := degIn_bridge_left hs y hs.2.2.2.2.1
    have hmy := hmax y (hA_sub hs.2.2.2.2.1)
    have h3 := hall y hs.2.2.2.2.1
    rw [if_pos rfl] at hdy; omega
  have hnk4B : ¬ (B.card = 4 ∧ ∀ v ∈ B, degIn G B v = 3) := by
    rintro ⟨_, hall⟩
    have hdz := degIn_bridge_left (bridge_split_symm hs) z hs.2.2.2.2.2.1
    have hmz := hmax z (hB_sub hs.2.2.2.2.2.1)
    have h3 := hall z hs.2.2.2.2.2.1
    rw [if_pos rfl] at hdz; omega
  obtain ⟨hpA, hleA, _⟩ := uncolorable_deficit A.card A rfl hA_ne hs.2.2.1 hmaxA hnk4A huncA
  obtain ⟨hpB, hleB, _⟩ := uncolorable_deficit B.card B rfl hB_ne hs.2.2.2.1 hmaxB hnk4B huncB
  have hpU := pCount_bridge_split hs hmax
  have hdefA : 3 * (pCount G A - 2) = A.card := by omega
  have hdefB : 3 * (pCount G B - 2) = B.card := by omega
  have hgeA := zero_deficit_deg_ge_two A.card A rfl hA_ne hs.2.2.1 hmaxA hnk4A huncA hdefA
  have hgeB := zero_deficit_deg_ge_two B.card B rfl hB_ne hs.2.2.2.1 hmaxB hnk4B huncB hdefB
  have hdyU := degIn_bridge_left hs y hs.2.2.2.2.1
  have hdzU := degIn_bridge_left (bridge_split_symm hs) z hs.2.2.2.2.2.1
  have hdyA : degIn G A y = 2 := by
    have h1 := hgeA y hs.2.2.2.2.1
    have h2 := hmax y (hA_sub hs.2.2.2.2.1)
    rw [if_pos rfl] at hdyU; omega
  have hdzB : degIn G B z = 2 := by
    have h1 := hgeB z hs.2.2.2.2.2.1
    have h2 := hmax z (hB_sub hs.2.2.2.2.2.1)
    rw [if_pos rfl] at hdzU; omega
  obtain ⟨hTA_ne, hcharA⟩ := zero_deficit_char A.card A rfl hA_ne hs.2.2.1 hmaxA hnk4A huncA hdefA y hs.2.2.2.2.1 hdyA
  obtain ⟨hTB_ne, hcharB⟩ := zero_deficit_char B.card B rfl hB_ne hs.2.2.2.1 hmaxB hnk4B huncB hdefB z hs.2.2.2.2.2.1 hdzB
  let TU := U.filter (fun v => degIn G U v = 2)
  let TA := A.filter (fun v => v ≠ y ∧ degIn G A v = 2)
  let TB := B.filter (fun v => v ≠ z ∧ degIn G B v = 2)
  have hTU_eq : TU = TA ∪ TB := by
    ext v
    simp only [TU, TA, TB, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro ⟨hvU, hdvU⟩
      rw [← hs.1] at hvU
      rcases Finset.mem_union.mp hvU with hvA | hvB
      · have hvy : v ≠ y := by intro heq; subst heq; rw [if_pos rfl] at hdyU; omega
        have hd := degIn_bridge_left hs v hvA
        rw [if_neg hvy] at hd
        exact Or.inl ⟨hvA, hvy, by omega⟩
      · have hvz : v ≠ z := by intro heq; subst heq; rw [if_pos rfl] at hdzU; omega
        have hd := degIn_bridge_left (bridge_split_symm hs) v hvB
        rw [if_neg hvz] at hd
        exact Or.inr ⟨hvB, hvz, by omega⟩
    · rintro (⟨hvA, hvy, hdvA⟩ | ⟨hvB, hvz, hdvB⟩)
      · have hd := degIn_bridge_left hs v hvA
        rw [if_neg hvy] at hd
        exact ⟨hA_sub hvA, by omega⟩
      · have hd := degIn_bridge_left (bridge_split_symm hs) v hvB
        rw [if_neg hvz] at hd
        exact ⟨hB_sub hvB, by omega⟩
  have hTU_ne : TU.Nonempty := by
    rw [hTU_eq]
    exact hTA_ne.mono Finset.subset_union_left
  refine ⟨hTU_ne, ?_⟩
  intro f hf3
  have hfy : f y = none := hf3 y (hA_sub hs.2.2.2.2.1) (by rw [if_pos rfl] at hdyU; omega)
  have hfz : f z = none := hf3 z (hB_sub hs.2.2.2.2.2.1) (by rw [if_pos rfl] at hdzU; omega)
  have hf3A : ∀ v ∈ A, degIn G A v = 3 → f v = none := by
    intro v hv hd3
    have hdU := degIn_bridge_left hs v hv
    have hm := hmax v (hA_sub hv)
    exact hf3 v (hA_sub hv) (by omega)
  have hf3B : ∀ v ∈ B, degIn G B v = 3 → f v = none := by
    intro v hv hd3
    have hdU := degIn_bridge_left (bridge_split_symm hs) v hv
    have hm := hmax v (hB_sub hv)
    exact hf3 v (hB_sub hv) (by omega)
  let oA : Option (Fin 3) := if h : ∃ b : Fin 3, ∀ v ∈ TA, f v = some b then some (Classical.choose h) else none
  let oB : Option (Fin 3) := if h : ∃ b : Fin 3, ∀ v ∈ TB, f v = some b then some (Classical.choose h) else none
  have hoA_some : ∀ b : Fin 3, oA = some b ↔ ∀ v ∈ TA, f v = some b := by
    intro b
    unfold oA
    split_ifs with h
    · constructor
      · intro heq; rw [← Option.some.inj heq]; exact Classical.choose_spec h
      · intro hall; congr 1
        obtain ⟨v0, hv0⟩ := hTA_ne
        have h1 := Classical.choose_spec h v0 hv0
        have h2 := hall v0 hv0
        rw [h1] at h2; exact Option.some.inj h2
    · constructor
      · intro heq; cases heq
      · intro hall; exact (h ⟨b, hall⟩).elim
  have hoB_some : ∀ b : Fin 3, oB = some b ↔ ∀ v ∈ TB, f v = some b := by
    intro b
    unfold oB
    split_ifs with h
    · constructor
      · intro heq; rw [← Option.some.inj heq]; exact Classical.choose_spec h
      · intro hall; congr 1
        obtain ⟨v0, hv0⟩ := hTB_ne
        have h1 := Classical.choose_spec h v0 hv0
        have h2 := hall v0 hv0
        rw [h1] at h2; exact Option.some.inj h2
    · constructor
      · intro heq; cases heq
      · intro hall; exact (h ⟨b, hall⟩).elim
  have hA_opt : ∀ a : Fin 3, (¬ ∃ b : Fin 3, b ≠ a ∧ ∀ v ∈ TA, f v = some b) ↔ (oA = none ∨ oA = some a) := by
    intro a
    cases h : oA with
    | none =>
      simp only [true_or, iff_true]
      rintro ⟨b, _, hall⟩
      have := (hoA_some b).mpr hall
      rw [h] at this; cases this
    | some b0 =>
      simp only [reduceCtorEq, Option.some.injEq, false_or]
      constructor
      · intro hnot
        by_contra hne
        exact hnot ⟨b0, hne, (hoA_some b0).mp h⟩
      · rintro rfl ⟨b, hba, hall⟩
        have := (hoA_some b).mpr hall
        rw [h] at this
        exact hba (Option.some.inj this).symm
  have hB_opt : ∀ a : Fin 3, (¬ ∃ b : Fin 3, b ≠ a ∧ ∀ v ∈ TB, f v = some b) ↔ (oB = none ∨ oB = some a) := by
    intro a
    cases h : oB with
    | none =>
      simp only [true_or, iff_true]
      rintro ⟨b, _, hall⟩
      have := (hoB_some b).mpr hall
      rw [h] at this; cases this
    | some b0 =>
      simp only [reduceCtorEq, Option.some.injEq, false_or]
      constructor
      · intro hnot
        by_contra hne
        exact hnot ⟨b0, hne, (hoB_some b0).mp h⟩
      · rintro rfl ⟨b, hba, hall⟩
        have := (hoB_some b).mpr hall
        rw [h] at this
        exact hba (Option.some.inj this).symm
  have hcol_iff : Colorable G U (Forb f) ↔
      ∃ a b : Fin 3, a ≠ b ∧ (oA = none ∨ oA = some a) ∧ (oB = none ∨ oB = some b) := by
    constructor
    · rintro ⟨c, hcL, hcadj⟩
      refine ⟨c y, c z, hcadj y (hA_sub hs.2.2.2.2.1) z (hB_sub hs.2.2.2.2.2.1) hs.2.2.2.2.2.2.1, ?_, ?_⟩
      · rw [← hA_opt (c y), ← hcharA f hfy hf3A (c y)]
        exact ⟨c, fun v hv => hcL v (hA_sub hv), fun u hu v hv ha => hcadj u (hA_sub hu) v (hA_sub hv) ha, rfl⟩
      · rw [← hB_opt (c z), ← hcharB f hfz hf3B (c z)]
        exact ⟨c, fun v hv => hcL v (hB_sub hv), fun u hu v hv ha => hcadj u (hB_sub hu) v (hB_sub hv) ha, rfl⟩
    · rintro ⟨a, b, hab, hoAa, hoBb⟩
      rw [← hA_opt a, ← hcharA f hfy hf3A a] at hoAa
      rw [← hB_opt b, ← hcharB f hfz hf3B b] at hoBb
      obtain ⟨cA, hcAL, hcAadj, hcy⟩ := hoAa
      obtain ⟨cB, hcBL, hcBadj, hcz⟩ := hoBb
      refine ⟨fun v => if v ∈ A then cA v else cB v, ?_, ?_⟩
      · intro v hv
        rw [← hs.1] at hv
        by_cases hvA : v ∈ A
        · simp [hvA, hcAL v hvA]
        · have hvB : v ∈ B := (Finset.mem_union.mp hv).resolve_left hvA
          simp [hvA, hcBL v hvB]
      · intro u hu v hv hadj
        rw [← hs.1] at hu hv
        by_cases huA : u ∈ A <;> by_cases hvA : v ∈ A
        · simp [huA, hvA, hcAadj u huA v hvA hadj]
        · have hvB : v ∈ B := (Finset.mem_union.mp hv).resolve_left hvA
          have ⟨huy, hvz⟩ := hs.2.2.2.2.2.2.2 u huA v hvB hadj
          subst huy; subst hvz; simp [huA, hvA, hcy, hcz, hab]
        · have huB : u ∈ B := (Finset.mem_union.mp hu).resolve_left huA
          have ⟨hvy, huz⟩ := hs.2.2.2.2.2.2.2 v hvA u huB hadj.symm
          subst hvy; subst huz; simp [huA, hvA, hcy, hcz, Ne.symm hab]
        · have huB : u ∈ B := (Finset.mem_union.mp hu).resolve_left huA
          have hvB : v ∈ B := (Finset.mem_union.mp hv).resolve_left hvA
          simp [huA, hvA, hcBadj u huB v hvB hadj]
  rw [hcol_iff, opt2_neq_char]
  apply not_congr
  apply exists_congr
  intro b
  rw [hoA_some b, hoB_some b]
  change ((∀ v ∈ TA, f v = some b) ∧ (∀ v ∈ TB, f v = some b)) ↔ ∀ v ∈ TU, f v = some b
  rw [hTU_eq]
  simp only [Finset.mem_union]
  constructor
  · rintro ⟨hA, hB⟩ v (hv | hv)
    · exact hA v hv
    · exact hB v hv
  · intro hall
    exact ⟨fun v hv => hall v (Or.inl hv), fun v hv => hall v (Or.inr hv)⟩

lemma not_colorable_k4 {G : SimpleGraph V} [DecidableRel G.Adj] {C : Finset V}
    (hcard : C.card = 4) (hreg : ∀ v ∈ C, degIn G C v = 3)
    (c : V → Fin 3) (hadj : ∀ u ∈ C, ∀ v ∈ C, G.Adj u v → c u ≠ c v) : False := by
  have hinj : Set.InjOn c (C : Set V) := by
    intro u hu v hv hce
    by_contra hne
    have hsub : C.filter (fun w => G.Adj u w) ⊆ C.erase u := by
      intro w hw
      have ⟨hwC, haw⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_erase.mpr ⟨G.ne_of_adj haw.symm, hwC⟩
    have hcardE : (C.erase u).card = 3 := by rw [Finset.card_erase_of_mem hu]; omega
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcardE]; exact (hreg u hu).ge)
    have hvE : v ∈ C.erase u := Finset.mem_erase.mpr ⟨Ne.symm hne, hv⟩
    rw [← heq] at hvE
    exact hadj u hu v hv (Finset.mem_filter.mp hvE).2 hce
  have hle : C.card ≤ (Finset.univ : Finset (Fin 3)).card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_univ _
  rw [Finset.card_univ, Fintype.card_fin] at hle
  omega

lemma main_proof_aux (k n : Nat) (G : SimpleGraph (Fin k ⊕ Fin n)) [DecidableRel G.Adj]
    (hdeg3 : ∀ v : Fin n, (Finset.univ.filter (fun w => G.Adj (Sum.inr v) w)).card ≤ 3) :
    let inc := fun i : Fin k => (Finset.univ.filter (fun v : Fin n => G.Adj (Sum.inl i) (Sum.inr v))).card
    let b := Finset.univ.sum inc
    let active := Finset.univ.filter (fun i => 0 < inc i)
    let top := 3 * (b - 2)
    let ext := fun (S : Finset (Fin n)) (x : Fin k → Fin 3) =>
      let keep : (Fin k ⊕ Fin n) → Prop := Sum.elim (fun _ => True) (fun v => v ∈ S)
      ∃ c : (Fin k ⊕ Fin n) → Fin 3, (∀ i, c (Sum.inl i) = x i) ∧
        ∀ u v, keep u → keep v → G.Adj u v → c u ≠ c v
    let faithful := fun S : Finset (Fin n) => ∀ x, ext S x ↔ ext Finset.univ x
    let least := fun h : Nat =>
      (∃ S, faithful S ∧ S.card = h) ∧ ∀ S, faithful S → h ≤ S.card
    5 ≤ b → (∀ S, faithful S → top - 2 ≤ S.card) →
    ∃ pattern : Fin k → Fin 3,
      (((active.image pattern).card = 1 ∧ least top) ∨
        ((active.image pattern).card = 3 ∧ least (top - 2))) ∧
      ∀ x, ext Finset.univ x ↔
        (∀ i j, G.Adj (Sum.inl i) (Sum.inl j) → x i ≠ x j) ∧
        ¬ ∃ p : Equiv.Perm (Fin 3), ∀ i ∈ active, x i = p (pattern i) := by
  intro inc b active top ext faithful least hb5 hlow
  haveI : DecidableRel (G.comap Sum.inr).Adj := fun u v => inferInstanceAs (Decidable (G.Adj (Sum.inr u) (Sum.inr v)))
  let H : SimpleGraph (Fin n) := G.comap Sum.inr
  let cross : Fin n → Finset (Fin k) := fun v => Finset.univ.filter (fun i => G.Adj (Sum.inl i) (Sum.inr v))
  let Lx : (Fin k → Fin 3) → Fin n → Finset (Fin 3) := fun x v =>
    Finset.univ.filter (fun c => ∀ i ∈ cross v, x i ≠ c)
  let PropL : (Fin k → Fin 3) → Prop := fun x => ∀ i j : Fin k, G.Adj (Sum.inl i) (Sum.inl j) → x i ≠ x j
  have hdeg_split : ∀ v : Fin n, (cross v).card + degIn H Finset.univ v ≤ 3 := by
    intro v
    have h1 : (cross v).card = ((Finset.univ.filter (fun w => G.Adj (Sum.inr v) w)).filter
        (fun w => Sum.isLeft w)).card := by
      refine Finset.card_bij (fun i _ => Sum.inl i) ?_ ?_ ?_
      · intro i hi
        have ha := (Finset.mem_filter.mp hi).2
        simp [ha.symm]
      · intro i1 _ i2 _ h; exact Sum.inl.inj h
      · intro w hw
        have ⟨hw1, hwl⟩ := Finset.mem_filter.mp hw
        cases w with
        | inl i => exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw1).2.symm⟩, rfl⟩
        | inr u => simp at hwl
    have h2 : degIn H Finset.univ v = ((Finset.univ.filter (fun w => G.Adj (Sum.inr v) w)).filter
        (fun w => ¬ Sum.isLeft w)).card := by
      unfold degIn
      refine Finset.card_bij (fun u _ => Sum.inr u) ?_ ?_ ?_
      · intro u hu
        have ha : G.Adj (Sum.inr v) (Sum.inr u) := (Finset.mem_filter.mp hu).2
        simp [ha]
      · intro u1 _ u2 _ h; exact Sum.inr.inj h
      · intro w hw
        have ⟨hw1, hwl⟩ := Finset.mem_filter.mp hw
        cases w with
        | inl i => simp at hwl
        | inr u => exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw1).2⟩, rfl⟩
    rw [h1, h2]
    have hdisj : Disjoint ((Finset.univ.filter (fun w => G.Adj (Sum.inr v) w)).filter (fun w => Sum.isLeft w))
        ((Finset.univ.filter (fun w => G.Adj (Sum.inr v) w)).filter (fun w => ¬ Sum.isLeft w)) := by
      refine Finset.disjoint_left.mpr ?_
      intro w hw1 hw2
      exact (Finset.mem_filter.mp hw2).2 (Finset.mem_filter.mp hw1).2
    have hunion : ((Finset.univ.filter (fun w => G.Adj (Sum.inr v) w)).filter (fun w => Sum.isLeft w)) ∪
        ((Finset.univ.filter (fun w => G.Adj (Sum.inr v) w)).filter (fun w => ¬ Sum.isLeft w)) =
        Finset.univ.filter (fun w => G.Adj (Sum.inr v) w) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_filter]
      by_cases hL : Sum.isLeft w <;> simp [hL]
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
    exact hdeg3 v
  have hsum_cross : Finset.univ.sum (fun v : Fin n => (cross v).card) = b := by
    have h1 : ∀ v : Fin n, (cross v).card = Finset.univ.sum (fun i : Fin k => if G.Adj (Sum.inl i) (Sum.inr v) then 1 else 0) := by
      intro v; exact Finset.card_filter (fun i => G.Adj (Sum.inl i) (Sum.inr v)) Finset.univ
    have h2 : ∀ i : Fin k, inc i = Finset.univ.sum (fun v : Fin n => if G.Adj (Sum.inl i) (Sum.inr v) then 1 else 0) := by
      intro i; exact Finset.card_filter (fun v => G.Adj (Sum.inl i) (Sum.inr v)) Finset.univ
    simp_rw [h1]
    rw [Finset.sum_comm]
    simp_rw [← h2]
    rfl
  have hext_iff : ∀ S x, ext S x ↔ PropL x ∧ Colorable H S (Lx x) := by
    intro S x
    constructor
    · rintro ⟨c, hcx, hcadj⟩
      refine ⟨fun i j ha => by rw [← hcx i, ← hcx j]; exact hcadj _ _ trivial trivial ha,
        fun v => c (Sum.inr v), ?_, ?_⟩
      · intro v hv
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => ?_⟩
        rw [← hcx i]
        exact hcadj _ _ trivial hv (Finset.mem_filter.mp hi).2
      · intro u hu v hv ha
        exact hcadj _ _ hu hv ha
    · rintro ⟨hpl, c', hc'L, hc'adj⟩
      refine ⟨Sum.elim x c', fun i => rfl, ?_⟩
      intro u v hu hv ha
      cases u with
      | inl i =>
        cases v with
        | inl j => exact hpl i j ha
        | inr w =>
          have hm := (Finset.mem_filter.mp (hc'L w hv)).2 i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)
          exact hm
      | inr w =>
        cases v with
        | inl i =>
          have hm := (Finset.mem_filter.mp (hc'L w hu)).2 i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.symm⟩)
          exact hm.symm
        | inr w2 => exact hc'adj w hu w2 hv ha
  have hLx_card : ∀ x v, 3 ≤ (Lx x v).card + (cross v).card := by
    intro x v
    have hcompl : (Lx x v) = Finset.univ \ (cross v).image x := by
      ext c
      simp only [Lx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_image, not_exists, not_and]
    rw [hcompl]
    have hs := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin 3)) ((cross v).image x)
    have hi : ((Finset.univ : Finset (Fin 3)) ∩ (cross v).image x).card = ((cross v).image x).card := by simp
    have him : ((cross v).image x).card ≤ (cross v).card := Finset.card_image_le
    simp only [Finset.card_univ, Fintype.card_fin] at hs
    omega
  have hex_min : ∃ S₀ : Finset (Fin n), faithful S₀ ∧ ∀ S, faithful S → S₀.card ≤ S.card := by
    classical
    let F := (Finset.univ : Finset (Finset (Fin n))).filter (fun S => faithful S)
    have hFne : F.Nonempty := ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ => Iff.rfl⟩⟩
    obtain ⟨S₀, hS₀F, hmin⟩ := Finset.exists_min_image F Finset.card hFne
    exact ⟨S₀, (Finset.mem_filter.mp hS₀F).2, fun S hS => hmin S (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩)⟩
  obtain ⟨S₀, hfaith₀, hmin₀⟩ := hex_min
  have hS₀_ge : top - 2 ≤ S₀.card := hlow S₀ hfaith₀
  have hS₀_ge7 : 7 ≤ S₀.card := by omega
  have hS₀_tight : ∀ v ∈ S₀, (cross v).card + degIn H S₀ v = 3 := by
    intro v hv
    have hle3 : (cross v).card + degIn H S₀ v ≤ 3 :=
      Nat.add_le_add_left (degIn_mono (Finset.subset_univ S₀) v) _ |>.trans (hdeg_split v)
    by_contra hne3
    have hlt3 : (cross v).card + degIn H S₀ v < 3 := by omega
    have hfaith_er : faithful (S₀.erase v) := by
      intro x
      rw [← hfaith₀ x, hext_iff, hext_iff]
      constructor
      · rintro ⟨hpl, c', hc'L, hc'adj⟩
        refine ⟨hpl, ?_⟩
        let used := ((S₀.erase v).filter (fun w => H.Adj v w)).image c'
        have hused_le : used.card ≤ degIn H S₀ v := by
          calc used.card ≤ ((S₀.erase v).filter (fun w => H.Adj v w)).card := Finset.card_image_le
            _ = degIn H (S₀.erase v) v := rfl
            _ ≤ degIn H S₀ v := degIn_mono (Finset.erase_subset v S₀) v
        have hLcard := hLx_card x v
        have havail : (Lx x v \ used).Nonempty := by
          apply Finset.card_pos.mp
          have hs := Finset.card_sdiff_add_card_inter (Lx x v) used
          have hi : (Lx x v ∩ used).card ≤ used.card := Finset.card_le_card Finset.inter_subset_right
          omega
        obtain ⟨col, hcol⟩ := havail
        have hcolL : col ∈ Lx x v := (Finset.mem_sdiff.mp hcol).1
        have hcolU : col ∉ used := (Finset.mem_sdiff.mp hcol).2
        refine ⟨Function.update c' v col, ?_, ?_⟩
        · intro u hu
          by_cases huv : u = v
          · subst huv; simp [hcolL]
          · rw [Function.update_of_ne huv]
            exact hc'L u (Finset.mem_erase.mpr ⟨huv, hu⟩)
        · intro u hu w hw hadj
          by_cases huv : u = v
          · subst huv
            have hwv : w ≠ u := H.ne_of_adj hadj.symm
            rw [Function.update_self, Function.update_of_ne hwv]
            intro heq
            exact hcolU (Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hwv, hw⟩, hadj⟩, heq.symm⟩)
          · by_cases hwv : w = v
            · subst hwv
              rw [Function.update_of_ne huv, Function.update_self]
              intro heq
              exact hcolU (Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨huv, hu⟩, hadj.symm⟩, heq⟩)
            · rw [Function.update_of_ne huv, Function.update_of_ne hwv]
              exact hc'adj u (Finset.mem_erase.mpr ⟨huv, hu⟩) w (Finset.mem_erase.mpr ⟨hwv, hw⟩) hadj
      · rintro ⟨hpl, c, hcL, hcadj⟩
        exact ⟨hpl, c, fun u hu => hcL u (Finset.mem_of_mem_erase hu),
          fun u hu w hw ha => hcadj u (Finset.mem_of_mem_erase hu) w (Finset.mem_of_mem_erase hw) ha⟩
    have hlt := Finset.card_erase_lt_of_mem hv
    have hge := hmin₀ (S₀.erase v) hfaith_er
    omega
  have hmaxS₀ : ∀ v ∈ S₀, degIn H S₀ v ≤ 3 := fun v hv => by have := hS₀_tight v hv; omega
  have hpS₀_eq_cross : pCount H S₀ = S₀.sum (fun v => (cross v).card) := by
    unfold pCount
    apply Finset.sum_congr rfl
    intro v hv
    have := hS₀_tight v hv; omega
  have hpS₀_le_b : pCount H S₀ ≤ b := by
    rw [hpS₀_eq_cross, ← hsum_cross]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ S₀)
  have hcomp_prop : ∀ C : Finset (Fin n), C ⊆ S₀ → C.Nonempty → ConnIn H C →
      (∀ u ∈ C, ∀ v ∈ S₀ \ C, ¬ H.Adj u v) →
      (∀ v ∈ C, degIn H C v = degIn H S₀ v) ∧
      Uncolorable H C ∧
      ¬ (C.card = 4 ∧ ∀ v ∈ C, degIn H C v = 3) := by
    intro C hCsub hCne hCconn hCiso
    have hdegEq : ∀ v ∈ C, degIn H C v = degIn H S₀ v := by
      intro v hv
      unfold degIn
      congr 1
      ext w
      simp only [Finset.mem_filter]
      constructor
      · intro ⟨hw, ha⟩; exact ⟨hCsub hw, ha⟩
      · intro ⟨hw, ha⟩
        refine ⟨?_, ha⟩
        by_contra hnot
        exact hCiso v hv w (Finset.mem_sdiff.mpr ⟨hw, hnot⟩) ha
    have hUncC : Uncolorable H C := by
      by_contra hnotU
      have hallC : ∀ x, Colorable H C (Lx x) := by
        intro x
        by_contra hnc
        apply hnotU
        refine ⟨Lx x, ?_, hnc⟩
        intro v hv
        have h1 := hLx_card x v
        have h2 := hS₀_tight v (hCsub hv)
        rw [hdegEq v hv]; omega
      have hfaith_diff : faithful (S₀ \ C) := by
        intro x
        rw [← hfaith₀ x, hext_iff, hext_iff]
        constructor
        · rintro ⟨hpl, cR, hcRL, hcRadj⟩
          obtain ⟨cC, hcCL, hcCadj⟩ := hallC x
          refine ⟨hpl, fun v => if v ∈ C then cC v else cR v, ?_, ?_⟩
          · intro v hv
            by_cases hvC : v ∈ C
            · simp [hvC, hcCL v hvC]
            · simp [hvC, hcRL v (Finset.mem_sdiff.mpr ⟨hv, hvC⟩)]
          · intro u hu v hv ha
            by_cases huC : u ∈ C <;> by_cases hvC : v ∈ C
            · simp [huC, hvC, hcCadj u huC v hvC ha]
            · exact (hCiso u huC v (Finset.mem_sdiff.mpr ⟨hv, hvC⟩) ha).elim
            · exact (hCiso v hvC u (Finset.mem_sdiff.mpr ⟨hu, huC⟩) ha.symm).elim
            · simp [huC, hvC, hcRadj u (Finset.mem_sdiff.mpr ⟨hu, huC⟩) v (Finset.mem_sdiff.mpr ⟨hv, hvC⟩) ha]
        · rintro ⟨hpl, c, hcL, hcadj⟩
          exact ⟨hpl, c, fun v hv => hcL v (Finset.mem_sdiff.mp hv).1,
            fun u hu v hv ha => hcadj u (Finset.mem_sdiff.mp hu).1 v (Finset.mem_sdiff.mp hv).1 ha⟩
      have hge := hmin₀ (S₀ \ C) hfaith_diff
      have hcard_sdiff : (S₀ \ C).card = S₀.card - C.card := by rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hCsub]
      have hCpos : 0 < C.card := Finset.card_pos.mpr hCne
      omega
    have hnk4C : ¬ (C.card = 4 ∧ ∀ v ∈ C, degIn H C v = 3) := by
      rintro ⟨hC4, hCreg⟩
      have hfaithC : faithful C := by
        intro x
        rw [← hfaith₀ x, hext_iff, hext_iff]
        constructor
        · rintro ⟨_, c, _, hcadj⟩; exact (not_colorable_k4 hC4 hCreg c hcadj).elim
        · rintro ⟨_, c, _, hcadj⟩
          exact (not_colorable_k4 hC4 hCreg c (fun u hu v hv ha => hcadj u (hCsub hu) v (hCsub hv) ha)).elim
      have hge := hlow C hfaithC
      omega
    exact ⟨hdegEq, hUncC, hnk4C⟩
  have hunion_bound : ∀ m : Nat, ∀ W : Finset (Fin n), W.card = m → W ⊆ S₀ → W.Nonempty →
      (∀ u ∈ W, ∀ v ∈ S₀ \ W, ¬ H.Adj u v) →
      3 ≤ pCount H W ∧ W.card ≤ 3 * (pCount H W - 2) := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro W hcard hWsub hWne hWiso
      classical
      obtain ⟨u0, hu0⟩ := hWne
      let C := W.filter (fun v => ReachIn H W u0 v)
      let R := W \ C
      have hCsubW : C ⊆ W := Finset.filter_subset _ _
      have hCsub : C ⊆ S₀ := Finset.Subset.trans hCsubW hWsub
      have hCne : C.Nonempty := ⟨u0, Finset.mem_filter.mpr ⟨hu0, Relation.ReflTransGen.refl⟩⟩
      have hCR_noedge : ∀ u ∈ C, ∀ v ∈ R, ¬ H.Adj u v := by
        intro u hu v hv ha
        have ⟨huW, hru⟩ := Finset.mem_filter.mp hu
        have ⟨hvW, hvnotC⟩ := Finset.mem_sdiff.mp hv
        exact hvnotC (Finset.mem_filter.mpr ⟨hvW, Relation.ReflTransGen.tail hru ⟨huW, hvW, ha⟩⟩)
      have hCiso : ∀ u ∈ C, ∀ v ∈ S₀ \ C, ¬ H.Adj u v := by
        intro u hu v hv ha
        have ⟨hvS, hvnotC⟩ := Finset.mem_sdiff.mp hv
        by_cases hvW : v ∈ W
        · exact hCR_noedge u hu v (Finset.mem_sdiff.mpr ⟨hvW, hvnotC⟩) ha
        · exact hWiso u (hCsubW hu) v (Finset.mem_sdiff.mpr ⟨hvS, hvW⟩) ha
      have hCconn : ConnIn H C := by
        intro u hu v hv
        have hu1 := Finset.mem_filter.mp hu
        have hv1 := Finset.mem_filter.mp hv
        have hpath := Relation.ReflTransGen.trans (reachIn_symm hu1.2) hv1.2
        have hlift : ∀ x, ReachIn H W u x → ReachIn H C u x := by
          intro x hux
          induction hux with
          | refl => exact Relation.ReflTransGen.refl
          | @tail p q hup hpq ihp =>
            have hpC : p ∈ C := Finset.mem_filter.mpr ⟨hpq.1, Relation.ReflTransGen.trans hu1.2 hup⟩
            have hqC : q ∈ C := Finset.mem_filter.mpr ⟨hpq.2.1, Relation.ReflTransGen.tail (Relation.ReflTransGen.trans hu1.2 hup) hpq⟩
            exact Relation.ReflTransGen.tail ihp ⟨hpC, hqC, hpq.2.2⟩
        exact hlift v hpath
      obtain ⟨hdegEqC, hUncC, hnk4C⟩ := hcomp_prop C hCsub hCne hCconn hCiso
      have hmaxC : ∀ v ∈ C, degIn H C v ≤ 3 := fun v hv => by rw [hdegEqC v hv]; exact hmaxS₀ v (hCsub hv)
      obtain ⟨hpC, hleC, _⟩ := uncolorable_deficit C.card C rfl hCne hCconn hmaxC hnk4C hUncC
      by_cases hRemp : R = ∅
      · have hCW : C = W := by
          ext v; simp only [R, Finset.ext_iff, Finset.mem_sdiff, Finset.notMem_empty, iff_false] at hRemp
          exact ⟨fun h => hCsubW h, fun h => by by_contra hn; exact hRemp v ⟨h, hn⟩⟩
        rw [← hCW]; exact ⟨hpC, hleC⟩
      · have hRne : R.Nonempty := Finset.nonempty_iff_ne_empty.mpr hRemp
        have hRsubW : R ⊆ W := Finset.sdiff_subset
        have hRsub : R ⊆ S₀ := Finset.Subset.trans hRsubW hWsub
        have hRiso : ∀ u ∈ R, ∀ v ∈ S₀ \ R, ¬ H.Adj u v := by
          intro u hu v hv ha
          have ⟨hvS, hvnotR⟩ := Finset.mem_sdiff.mp hv
          by_cases hvW : v ∈ W
          · have hvC : v ∈ C := by by_contra hnc; exact hvnotR (Finset.mem_sdiff.mpr ⟨hvW, hnc⟩)
            exact hCR_noedge v hvC u hu ha.symm
          · exact hWiso u (hRsubW hu) v (Finset.mem_sdiff.mpr ⟨hvS, hvW⟩) ha
        have hdisjCR : Disjoint C R := Finset.disjoint_sdiff
        have hunionCR : C ∪ R = W := Finset.union_sdiff_of_subset hCsubW
        have hcardCR : C.card + R.card = W.card := by rw [← hunionCR, Finset.card_union_of_disjoint hdisjCR]
        have hRlt : R.card < m := by have := Finset.card_pos.mpr hCne; omega
        obtain ⟨hpR, hleR⟩ := ih R.card hRlt R rfl hRsub hRne hRiso
        have hdegW : ∀ v ∈ C, degIn H W v = degIn H C v := by
          intro v hv
          have h1 := degIn_mono (G := H) hCsubW v
          have h2 := degIn_mono (G := H) hWsub v
          have h3 := hdegEqC v hv
          omega
        have hdegR : ∀ v ∈ R, degIn H W v = degIn H R v := by
          intro v hv
          unfold degIn
          congr 1
          ext w
          simp only [Finset.mem_filter]
          constructor
          · intro ⟨hwW, ha⟩
            refine ⟨Finset.mem_sdiff.mpr ⟨hwW, fun hwC => hCR_noedge w hwC v hv ha.symm⟩, ha⟩
          · intro ⟨hwR, ha⟩; exact ⟨hRsubW hwR, ha⟩
        have hpW : pCount H W = pCount H C + pCount H R := by
          have h1 : pCount H W = (C ∪ R).sum (fun v => 3 - degIn H W v) := by rw [hunionCR]; rfl
          rw [h1, Finset.sum_union hdisjCR]
          unfold pCount
          congr 1
          · exact Finset.sum_congr rfl fun v hv => by rw [hdegW v hv]
          · exact Finset.sum_congr rfl fun v hv => by rw [hdegR v hv]
        omega
  have hS₀_ne : S₀.Nonempty := Finset.card_pos.mp (by omega)
  have hS₀_conn : ConnIn H S₀ := by
    classical
    obtain ⟨u0, hu0⟩ := hS₀_ne
    let C := S₀.filter (fun v => ReachIn H S₀ u0 v)
    let R := S₀ \ C
    have hCsub : C ⊆ S₀ := Finset.filter_subset _ _
    have hCne : C.Nonempty := ⟨u0, Finset.mem_filter.mpr ⟨hu0, Relation.ReflTransGen.refl⟩⟩
    have hCR_noedge : ∀ u ∈ C, ∀ v ∈ R, ¬ H.Adj u v := by
      intro u hu v hv ha
      have ⟨huS, hru⟩ := Finset.mem_filter.mp hu
      have ⟨hvS, hvnotC⟩ := Finset.mem_sdiff.mp hv
      exact hvnotC (Finset.mem_filter.mpr ⟨hvS, Relation.ReflTransGen.tail hru ⟨huS, hvS, ha⟩⟩)
    have hCconn : ConnIn H C := by
      intro u hu v hv
      have hu1 := Finset.mem_filter.mp hu
      have hv1 := Finset.mem_filter.mp hv
      have hpath := Relation.ReflTransGen.trans (reachIn_symm hu1.2) hv1.2
      have hlift : ∀ x, ReachIn H S₀ u x → ReachIn H C u x := by
        intro x hux
        induction hux with
        | refl => exact Relation.ReflTransGen.refl
        | @tail p q hup hpq ihp =>
          have hpC : p ∈ C := Finset.mem_filter.mpr ⟨hpq.1, Relation.ReflTransGen.trans hu1.2 hup⟩
          have hqC : q ∈ C := Finset.mem_filter.mpr ⟨hpq.2.1, Relation.ReflTransGen.tail (Relation.ReflTransGen.trans hu1.2 hup) hpq⟩
          exact Relation.ReflTransGen.tail ihp ⟨hpC, hqC, hpq.2.2⟩
      exact hlift v hpath
    by_cases hRemp : R = ∅
    · have hCS : C = S₀ := by
        ext v; simp only [R, Finset.ext_iff, Finset.mem_sdiff, Finset.notMem_empty, iff_false] at hRemp
        exact ⟨fun h => hCsub h, fun h => by by_contra hn; exact hRemp v ⟨h, hn⟩⟩
      rw [← hCS]; exact hCconn
    · exfalso
      have hRne : R.Nonempty := Finset.nonempty_iff_ne_empty.mpr hRemp
      have hRsub : R ⊆ S₀ := Finset.sdiff_subset
      have hRiso : ∀ u ∈ R, ∀ v ∈ S₀ \ R, ¬ H.Adj u v := by
        intro u hu v hv ha
        have ⟨hvS, hvnotR⟩ := Finset.mem_sdiff.mp hv
        have hvC : v ∈ C := by by_contra hnc; exact hvnotR (Finset.mem_sdiff.mpr ⟨hvS, hnc⟩)
        exact hCR_noedge v hvC u hu ha.symm
      obtain ⟨hdegEqC, hUncC, hnk4C⟩ := hcomp_prop C hCsub hCne hCconn hCR_noedge
      have hmaxC : ∀ v ∈ C, degIn H C v ≤ 3 := fun v hv => by rw [hdegEqC v hv]; exact hmaxS₀ v (hCsub hv)
      obtain ⟨hpC, hleC, _⟩ := uncolorable_deficit C.card C rfl hCne hCconn hmaxC hnk4C hUncC
      obtain ⟨hpR, hleR⟩ := hunion_bound R.card R rfl hRsub hRne hRiso
      have hdisjCR : Disjoint C R := Finset.disjoint_sdiff
      have hunionCR : C ∪ R = S₀ := Finset.union_sdiff_of_subset hCsub
      have hcardCR : C.card + R.card = S₀.card := by rw [← hunionCR, Finset.card_union_of_disjoint hdisjCR]
      have hdegR : ∀ v ∈ R, degIn H S₀ v = degIn H R v := by
        intro v hv
        unfold degIn
        congr 1
        ext w
        simp only [Finset.mem_filter]
        constructor
        · intro ⟨hwS, ha⟩
          exact ⟨Finset.mem_sdiff.mpr ⟨hwS, fun hwC => hCR_noedge w hwC v hv ha.symm⟩, ha⟩
        · intro ⟨hwR, ha⟩; exact ⟨hRsub hwR, ha⟩
      have hpS₀ : pCount H S₀ = pCount H C + pCount H R := by
        have h1 : pCount H S₀ = (C ∪ R).sum (fun v => 3 - degIn H S₀ v) := by rw [hunionCR]; rfl
        rw [h1, Finset.sum_union hdisjCR]
        unfold pCount
        congr 1
        · exact Finset.sum_congr rfl fun v hv => by rw [hdegEqC v hv]
        · exact Finset.sum_congr rfl fun v hv => by rw [hdegR v hv]
      omega
  have hS₀_iso : ∀ u ∈ S₀, ∀ v ∈ S₀ \ S₀, ¬ H.Adj u v := by simp
  obtain ⟨_, hUncS₀, hnk4S₀⟩ := hcomp_prop S₀ (Finset.Subset.refl S₀) hS₀_ne hS₀_conn hS₀_iso
  obtain ⟨hpS₀_ge3, hS₀_le_top, ⟨mDef, hmDef⟩⟩ :=
    uncolorable_deficit S₀.card S₀ rfl hS₀_ne hS₀_conn hmaxS₀ hnk4S₀ hUncS₀
  have hpS₀_eq_b : pCount H S₀ = b := by omega
  have hcross_out : ∀ v : Fin n, v ∉ S₀ → cross v = ∅ := by
    intro v hv
    have hsum_rest : (Finset.univ \ S₀).sum (fun w => (cross w).card) = 0 := by
      have h1 : S₀.sum (fun w => (cross w).card) + (Finset.univ \ S₀).sum (fun w => (cross w).card) = b := by
        rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset (Finset.subset_univ S₀), hsum_cross]
      omega
    have hv0 : (cross v).card = 0 :=
      (Finset.sum_eq_zero_iff.mp hsum_rest) v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩)
    exact Finset.card_eq_zero.mp hv0
  have hactive_iff : ∀ i : Fin k, i ∈ active ↔ ∃ v ∈ S₀, i ∈ cross v := by
    intro i
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and, inc, Finset.card_pos, cross]
    constructor
    · rintro ⟨v, hv⟩
      have ha := (Finset.mem_filter.mp hv).2
      have hvS : v ∈ S₀ := by
        by_contra hnot
        have hmem : i ∈ cross v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
        rw [hcross_out v hnot] at hmem
        exact Finset.notMem_empty i hmem
      exact ⟨v, hvS, ha⟩
    · rintro ⟨v, _, ha⟩
      exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
  have hactive_ne : active.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hb0 : b = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_contra hpos
      have : i ∈ active := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hpos⟩
      rw [hne] at this
      exact Finset.notMem_empty i this
    omega
  have hm01 : mDef = 0 ∨ mDef = 1 := by omega
  rcases hm01 with hm0 | hm1
  · have hS₀_top : S₀.card = top := by omega
    have hdef0 : 3 * (pCount H S₀ - 2) = S₀.card := by omega
    have hp5 : 5 ≤ pCount H S₀ := by omega
    have hge2 := zero_deficit_deg_ge_two S₀.card S₀ rfl hS₀_ne hS₀_conn hmaxS₀ hnk4S₀ hUncS₀ hdef0
    obtain ⟨_, hchar0⟩ := zero_deficit_whole hS₀_ne hS₀_conn hmaxS₀ hnk4S₀ hUncS₀ hdef0 hp5
    refine ⟨fun _ => 0, Or.inl ⟨?_, ⟨⟨S₀, hfaith₀, hS₀_top⟩, fun S hS => by have := hmin₀ S hS; omega⟩⟩, ?_⟩
    · have heq : active.image (fun _ : Fin k => (0 : Fin 3)) = {0} := by
        ext c
        simp only [Finset.mem_image, Finset.mem_singleton]
        constructor
        · rintro ⟨_, _, rfl⟩; rfl
        · rintro rfl; obtain ⟨i0, hi0⟩ := hactive_ne; exact ⟨i0, hi0, rfl⟩
      rw [heq, Finset.card_singleton]
    · intro x
      rw [← hfaith₀ x, hext_iff]
      apply and_congr Iff.rfl
      let fx : Fin n → Option (Fin 3) := fun v =>
        if h : (cross v).Nonempty then some (x (Classical.choose h)) else none
      have hfx3 : ∀ v ∈ S₀, degIn H S₀ v = 3 → fx v = none := by
        intro v hv hd3
        have hc0 : (cross v).card = 0 := by have := hS₀_tight v hv; omega
        have hne : ¬ (cross v).Nonempty := by rw [Finset.nonempty_iff_ne_empty]; simp [Finset.card_eq_zero.mp hc0]
        simp [fx, hne]
      have hL_eq : ∀ v ∈ S₀, Lx x v = Forb fx v := by
        intro v hv
        have hd2 := hge2 v hv
        have ht := hS₀_tight v hv
        by_cases hc0 : (cross v).card = 0
        · have hemp : cross v = ∅ := Finset.card_eq_zero.mp hc0
          have hne : ¬ (cross v).Nonempty := by simp [hemp]
          ext c; simp [Lx, Forb, fx, hemp, hne]
        · have hc1 : (cross v).card = 1 := by omega
          obtain ⟨i0, hi0⟩ := Finset.card_eq_one.mp hc1
          have hne : (cross v).Nonempty := ⟨i0, by rw [hi0]; simp⟩
          have hch : Classical.choose hne = i0 :=
            Finset.mem_singleton.mp (hi0 ▸ Classical.choose_spec hne)
          have hfx_eq : fx v = some (x i0) := by
            simp only [fx, dif_pos hne, hch]
          ext c
          rw [Forb, hfx_eq]
          simp only [Lx, hi0, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton, forall_eq, Finset.mem_erase, and_true]
          exact ne_comm
      have hcol_eq : Colorable H S₀ (Lx x) ↔ Colorable H S₀ (Forb fx) := by
        constructor <;> rintro ⟨c, hcL, hcadj⟩
        · exact ⟨c, fun v hv => by rw [← hL_eq v hv]; exact hcL v hv, hcadj⟩
        · exact ⟨c, fun v hv => by rw [hL_eq v hv]; exact hcL v hv, hcadj⟩
      rw [hcol_eq, hchar0 fx hfx3]
      apply not_congr
      constructor
      · rintro ⟨c0, hall⟩
        refine ⟨Equiv.swap 0 c0, fun i hi => ?_⟩
        obtain ⟨v, hvS, hiv⟩ := (hactive_iff i).mp hi
        have hd2 := hge2 v hvS
        have ht := hS₀_tight v hvS
        have hcpos : 1 ≤ (cross v).card := Finset.card_pos.mpr ⟨i, hiv⟩
        have hdv2 : degIn H S₀ v = 2 := by omega
        have hc1 : (cross v).card = 1 := by omega
        obtain ⟨i0, hi0⟩ := Finset.card_eq_one.mp hc1
        have hii0 : i = i0 := by rw [hi0, Finset.mem_singleton] at hiv; exact hiv
        subst hii0
        have hne : (cross v).Nonempty := ⟨i, hiv⟩
        have hch : Classical.choose hne = i :=
          Finset.mem_singleton.mp (hi0 ▸ Classical.choose_spec hne)
        have hfv := hall v (Finset.mem_filter.mpr ⟨hvS, hdv2⟩)
        simp only [fx, dif_pos hne, hch, Option.some.injEq] at hfv
        rw [hfv, Equiv.swap_apply_left]
      · rintro ⟨p, hall⟩
        refine ⟨p 0, fun v hv => ?_⟩
        have ⟨hvS, hdv2⟩ := Finset.mem_filter.mp hv
        have hc1 : (cross v).card = 1 := by have := hS₀_tight v hvS; omega
        obtain ⟨i0, hi0⟩ := Finset.card_eq_one.mp hc1
        have hne : (cross v).Nonempty := ⟨i0, by rw [hi0]; simp⟩
        have hch : Classical.choose hne = i0 :=
          Finset.mem_singleton.mp (hi0 ▸ Classical.choose_spec hne)
        have hi0_act : i0 ∈ active := (hactive_iff i0).mpr ⟨v, hvS, by rw [hi0]; simp⟩
        simp only [fx, dif_pos hne, hch, Option.some.injEq]
        exact hall i0 hi0_act
  · have hS₀_top2 : S₀.card = top - 2 := by omega
    have hdef2 : 3 * (pCount H S₀ - 2) = S₀.card + 2 := by omega
    let C : Fin n → List (Finset (Fin k)) := fun v => (cross v).toList.map (fun i => {i})
    have hClen : ∀ v ∈ S₀, (C v).length = 3 - degIn H S₀ v := by
      intro v hv
      simp only [C, List.length_map, Finset.length_toList]
      have := hS₀_tight v hv; omega
    have hCne : ∀ v ∈ S₀, ∀ s ∈ C v, s.Nonempty := by
      intro v _ s hs
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
      exact ⟨i, by simp⟩
    obtain ⟨P, hPne, hPunion, hPchar⟩ :=
      two_deficit_char S₀.card S₀ rfl hS₀_ne hS₀_conn hmaxS₀ hnk4S₀ hUncS₀ hdef2 C hClen hCne
    have hUunion : S₀.biUnion (fun v => unionList (C v)) = active := by
      ext i
      rw [hactive_iff i, Finset.mem_biUnion]
      apply exists_congr
      intro v
      apply and_congr Iff.rfl
      rw [mem_unionList]
      simp only [C, List.mem_map]
      constructor
      · rintro ⟨s, ⟨j, hj, rfl⟩, his⟩
        rw [Finset.mem_singleton.mp his]
        exact Finset.mem_toList.mp hj
      · intro hi
        exact ⟨{i}, ⟨i, Finset.mem_toList.mpr hi, rfl⟩, by simp⟩
    rw [hUunion] at hPunion
    have hL_eq : ∀ x v, LOfCons C x v = Lx x v := by
      intro x v
      ext c
      simp only [LOfCons, Lx, C, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_map]
      constructor
      · intro h i hi heq
        exact h {i} ⟨i, Finset.mem_toList.mpr hi, rfl⟩ (fun j hj => by rw [Finset.mem_singleton.mp hj]; exact heq)
      · rintro h s ⟨i, hi, rfl⟩ hall
        exact h i (Finset.mem_toList.mp hi) (hall i (by simp))
    have hPdisj : ∀ m1 m2 : Fin 3, m1 ≠ m2 → Disjoint (P m1) (P m2) := by
      have hnot_emp : ¬ faithful ∅ := by
        intro hf
        have := hlow ∅ hf
        simp at this; omega
      have hex_x0 : ∃ x0 : Fin k → Fin 3, ¬ (ext ∅ x0 ↔ ext Finset.univ x0) := by
        by_contra hall; push_neg at hall; exact hnot_emp hall
      obtain ⟨x0, hx0⟩ := hex_x0
      have hnotU : ¬ ext Finset.univ x0 := by
        intro hU
        apply hx0
        refine ⟨fun _ => hU, fun _ => ?_⟩
        rw [hext_iff] at hU ⊢
        exact ⟨hU.1, fun _ => 0, fun _ h => (Finset.notMem_empty _ h).elim, fun _ h => (Finset.notMem_empty _ h).elim⟩
      have hE : ext ∅ x0 := by
        by_contra hnotE
        exact hx0 ⟨fun h => (hnotE h).elim, fun h => (hnotU h).elim⟩
      rw [hext_iff] at hE
      rw [← hfaith₀ x0, hext_iff] at hnotU
      have hnc0 : ¬ Colorable H S₀ (Lx x0) := fun hc => hnotU ⟨hE.1, hc⟩
      have hncC : ¬ Colorable H S₀ (LOfCons C x0) := by
        intro ⟨c, hcL, hcadj⟩
        exact hnc0 ⟨c, fun v hv => by rw [← hL_eq x0 v]; exact hcL v hv, hcadj⟩
      rw [hPchar x0, not_not] at hncC
      obtain ⟨p0, hp0⟩ := hncC
      intro m1 m2 hne
      refine Finset.disjoint_left.mpr ?_
      intro i hi1 hi2
      have h1 := hp0 m1 i hi1
      have h2 := hp0 m2 i hi2
      exact hne (p0.injective (h1.symm.trans h2))
    let pattern : Fin k → Fin 3 := fun i => if i ∈ P 0 then 0 else if i ∈ P 1 then 1 else 2
    have hpat_eq : ∀ m : Fin 3, ∀ i ∈ P m, pattern i = m := by
      intro m i hi
      fin_cases m
      · change i ∈ P 0 at hi
        change pattern i = 0
        simp [pattern, hi]
      · change i ∈ P 1 at hi
        change pattern i = 1
        have hnot0 : i ∉ P 0 := fun h0 => Finset.disjoint_left.mp (hPdisj 0 1 (by decide)) h0 hi
        simp [pattern, hnot0, hi]
      · change i ∈ P 2 at hi
        change pattern i = 2
        have hnot0 : i ∉ P 0 := fun h0 => Finset.disjoint_left.mp (hPdisj 0 2 (by decide)) h0 hi
        have hnot1 : i ∉ P 1 := fun h1 => Finset.disjoint_left.mp (hPdisj 1 2 (by decide)) h1 hi
        simp [pattern, hnot0, hnot1]
    refine ⟨pattern, Or.inr ⟨?_, ⟨⟨S₀, hfaith₀, hS₀_top2⟩, hlow⟩⟩, ?_⟩
    · have him : active.image pattern = Finset.univ := by
        ext m
        simp only [Finset.mem_image, Finset.mem_univ, iff_true]
        obtain ⟨i, hi⟩ := hPne m
        have hiA : i ∈ active := by rw [← hPunion]; exact Finset.mem_biUnion.mpr ⟨m, Finset.mem_univ _, hi⟩
        exact ⟨i, hiA, hpat_eq m i hi⟩
      rw [him, Finset.card_univ, Fintype.card_fin]
    · intro x
      rw [← hfaith₀ x, hext_iff]
      apply and_congr Iff.rfl
      have hcolC : Colorable H S₀ (Lx x) ↔ Colorable H S₀ (LOfCons C x) := by
        constructor <;> rintro ⟨c, hcL, hcadj⟩
        · exact ⟨c, fun v hv => by rw [hL_eq x v]; exact hcL v hv, hcadj⟩
        · exact ⟨c, fun v hv => by rw [← hL_eq x v]; exact hcL v hv, hcadj⟩
      rw [hcolC, hPchar x]
      apply not_congr
      apply exists_congr
      intro p
      constructor
      · intro hall i hi
        rw [← hPunion] at hi
        obtain ⟨m, _, him⟩ := Finset.mem_biUnion.mp hi
        rw [hpat_eq m i him]
        exact hall m i him
      · intro hall m i him
        have hiA : i ∈ active := by rw [← hPunion]; exact Finset.mem_biUnion.mpr ⟨m, Finset.mem_univ _, him⟩
        have := hall i hiA
        rwa [hpat_eq m i him] at this

lemma main_proof :
    (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (k n : Nat) (G : SimpleGraph (Fin k ⊕ Fin n)),
      (∀ v : Fin n, (Finset.univ.filter (fun w => G.Adj (Sum.inr v) w)).card ≤ 3) →
      let inc := fun i : Fin k => (Finset.univ.filter (fun v : Fin n => G.Adj (Sum.inl i) (Sum.inr v))).card
      let b := Finset.univ.sum inc
      let active := Finset.univ.filter (fun i => 0 < inc i)
      let top := 3 * (b - 2)
      let ext := fun (S : Finset (Fin n)) (x : Fin k → Fin 3) =>
        let keep : (Fin k ⊕ Fin n) → Prop := Sum.elim (fun _ => True) (fun v => v ∈ S)
        ∃ c : (Fin k ⊕ Fin n) → Fin 3, (∀ i, c (Sum.inl i) = x i) ∧
          ∀ u v, keep u → keep v → G.Adj u v → c u ≠ c v
      let faithful := fun S : Finset (Fin n) => ∀ x, ext S x ↔ ext Finset.univ x
      let least := fun h : Nat =>
        (∃ S, faithful S ∧ S.card = h) ∧ ∀ S, faithful S → h ≤ S.card
      5 ≤ b → (∀ S, faithful S → top - 2 ≤ S.card) →
      ∃ pattern : Fin k → Fin 3,
        (((active.image pattern).card = 1 ∧ least top) ∨
          ((active.image pattern).card = 3 ∧ least (top - 2))) ∧
        ∀ x, ext Finset.univ x ↔
          (∀ i j, G.Adj (Sum.inl i) (Sum.inl j) → x i ≠ x j) ∧
          ¬ ∃ p : Equiv.Perm (Fin 3), ∀ i ∈ active, x i = p (pattern i)) := by
  intro k n G hdeg3 inc b active top ext faithful least hb5 hlow
  letI : DecidableRel G.Adj := fun u v => Classical.propDecidable (G.Adj u v)
  have hact_eq : active = @Finset.filter (Fin k) (fun i => 0 < inc i) (fun i => Nat.decLt 0 (inc i)) Finset.univ := by
    ext i; simp [active]
  have him_eq : ∀ (s : Finset (Fin k)) (f : Fin k → Fin 3),
      @Finset.image (Fin k) (Fin 3) (fun a b => Classical.propDecidable (a = b)) f s =
      @Finset.image (Fin k) (Fin 3) (instDecidableEqFin 3) f s := by
    intro s f; ext y; simp [Finset.mem_image]
  obtain ⟨pattern, hpat, hiff⟩ := main_proof_aux k n G hdeg3 hb5 hlow
  refine ⟨pattern, ?_, ?_⟩
  · rw [hact_eq, him_eq]
    exact hpat
  · intro x
    rw [hact_eq]
    exact hiff x

end ZeroDeficitWholeAndMain

end PEqualNP.Outside.L_pcx_488

theorem PEqualNP.Outside.L_pcx_488 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (k n : Nat) (G : SimpleGraph (Fin k ⊕ Fin n)),
  (∀ v : Fin n, (Finset.univ.filter (fun w => G.Adj (Sum.inr v) w)).card ≤ 3) →
  let inc := fun i : Fin k => (Finset.univ.filter (fun v : Fin n => G.Adj (Sum.inl i) (Sum.inr v))).card
  let b := Finset.univ.sum inc
  let active := Finset.univ.filter (fun i => 0 < inc i)
  let top := 3 * (b - 2)
  let ext := fun (S : Finset (Fin n)) (x : Fin k → Fin 3) =>
    let keep : (Fin k ⊕ Fin n) → Prop := Sum.elim (fun _ => True) (fun v => v ∈ S)
    ∃ c : (Fin k ⊕ Fin n) → Fin 3, (∀ i, c (Sum.inl i) = x i) ∧
      ∀ u v, keep u → keep v → G.Adj u v → c u ≠ c v
  let faithful := fun S : Finset (Fin n) => ∀ x, ext S x ↔ ext Finset.univ x
  let least := fun h : Nat =>
    (∃ S, faithful S ∧ S.card = h) ∧ ∀ S, faithful S → h ≤ S.card
  5 ≤ b → (∀ S, faithful S → top - 2 ≤ S.card) →
  ∃ pattern : Fin k → Fin 3,
    (((active.image pattern).card = 1 ∧ least top) ∨
      ((active.image pattern).card = 3 ∧ least (top - 2))) ∧
    ∀ x, ext Finset.univ x ↔
      (∀ i j, G.Adj (Sum.inl i) (Sum.inl j) → x i ≠ x j) ∧
      ¬ ∃ p : Equiv.Perm (Fin 3), ∀ i ∈ active, x i = p (pattern i)) :=
  PEqualNP.Outside.L_pcx_488.main_proof
