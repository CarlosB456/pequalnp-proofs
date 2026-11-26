import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1599

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

-- Wire values of a gate list, evaluated from left to right on a given input word.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

-- The value of wire `i` of `C` on the input `x`.
def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

lemma gateVal_eq_wv (n : ℕ) (C : Circuit) (k : ℕ) (x : Fin n → Bool) :
    gateVal n C k x = wv n C x (n + k) := rfl

lemma wv_input {n : ℕ} {C : Circuit} {x : Fin n → Bool} {i : ℕ} (h : i < n) :
    wv n C x i = x ⟨i, h⟩ := by
  unfold wv
  rw [getD_wiresFrom_lt C.gates (List.ofFn x) i (by simpa using h)]
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]

lemma gateVal_gate {n : ℕ} (C : Circuit) {k : ℕ} (hk : k < C.gates.length) (x : Fin n → Bool) :
    gateVal n C k x =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
        if i < n + k then wv n C x i else false) := by
  have hgk : gateAt C k = C.gates[k] :=
    List.getD_eq_getElem C.gates ⟨GateOp.or, []⟩ hk
  have h := getD_wiresFrom_gate C.gates (List.ofFn x) k hk
  change (wiresFrom C.gates (List.ofFn x)).getD (n + k) false =
    (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then wv n C x i else false)
  rw [hgk]
  simpa [wv] using h

lemma graphFun_empty_eq {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (x : Fin n → Bool) :
    graphFun K ∅ x = decide (∃ u v, K.Adj u v ∧ x u = true ∧ x v = true) := by
  unfold graphFun
  simp

lemma graphFun_empty_adj {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] {u v : Fin n}
    (h : K.Adj u v) : graphFun K ∅ (pairInput u v) = true := by
  rw [graphFun_empty_eq, decide_eq_true_eq]
  exact ⟨u, v, h, by simp [pairInput], by simp [pairInput]⟩

lemma graphFun_empty_single {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (w : Fin n) :
    graphFun K ∅ (pairInput w w) = false := by
  rw [graphFun_empty_eq, decide_eq_false_iff_not]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [pairInput, decide_eq_true_eq] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> exact K.loopless.irrefl _ hab

-- A gate that is true at `1_uv` yields a true AND gate above it, or a true input that the
-- gate is still true at.
lemma descent {n : ℕ} (C : Circuit) (handor : AndOrOnly C) (u v : Fin n) :
    ∀ k, k < C.gates.length →
      gateVal n C k (pairInput u v) = true →
      (∃ i, i ≤ k ∧ (gateAt C i).op = GateOp.and ∧
        gateVal n C i (pairInput u v) = true) ∨
      (∃ w : Fin n, pairInput u v w = true ∧ gateVal n C k (pairInput w w) = true) := by
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ih hk htrue
  have hmem : gateAt C k ∈ C.gates := by
    rw [show gateAt C k = C.gates[k] from
      List.getD_eq_getElem C.gates ⟨GateOp.or, []⟩ hk]
    exact List.getElem_mem hk
  rcases handor (gateAt C k) hmem with hop | hop
  · exact Or.inl ⟨k, le_rfl, hop, htrue⟩
  · have hval := htrue
    rw [gateVal_gate C hk, hop] at hval
    simp only [GateOp.eval] at hval
    obtain ⟨b, hb, hbid⟩ := List.any_eq_true.1 hval
    obtain ⟨i, hi, hif⟩ := List.mem_map.1 hb
    have hbtrue : b = true := hbid
    have hfitrue : (if i < n + k then wv n C (pairInput u v) i else false) = true := by
      rw [hif, hbtrue]
    have hilt : i < n + k := by
      by_contra hge
      rw [if_neg hge] at hfitrue
      exact absurd hfitrue (by simp)
    have hwvtrue : wv n C (pairInput u v) i = true := by
      rwa [if_pos hilt] at hfitrue
    by_cases hin : i < n
    · refine Or.inr ⟨⟨i, hin⟩, ?_, ?_⟩
      · rw [← wv_input (C := C) (x := pairInput u v) hin]
        exact hwvtrue
      · simp only [gateVal_gate C hk, hop, GateOp.eval]
        apply List.any_eq_true.2
        refine ⟨true, List.mem_map.2 ⟨i, hi, ?_⟩, rfl⟩
        rw [if_pos hilt, wv_input (C := C) (x := pairInput ⟨i, hin⟩ ⟨i, hin⟩) hin]
        simp [pairInput]
    · push_neg at hin
      obtain ⟨k', rfl⟩ : ∃ k', i = n + k' := ⟨i - n, by omega⟩
      have hk'lt : k' < k := by omega
      have hk'len : k' < C.gates.length := by omega
      have htrue' : gateVal n C k' (pairInput u v) = true := by
        rw [gateVal_eq_wv]
        exact hwvtrue
      rcases ih k' hk'lt hk'len htrue' with ⟨i0, hi0, hand, htrue0⟩ | ⟨w, hxw, hkw⟩
      · exact Or.inl ⟨i0, by omega, hand, htrue0⟩
      · refine Or.inr ⟨w, hxw, ?_⟩
        simp only [gateVal_gate C hk, hop, GateOp.eval]
        apply List.any_eq_true.2
        refine ⟨true, List.mem_map.2 ⟨n + k', hi, ?_⟩, rfl⟩
        rw [if_pos hilt, ← gateVal_eq_wv]
        exact hkw

end PEqualNP.Outside.L_meta_1599

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.L_meta_1599 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      AndOrOnly C → circuitFun n C = graphFun G ∅ → EveryEdgeOwned n G C := by
  intro n G _ C handor hfun u v huv
  classical
  have hgf : graphFun G ∅ (pairInput u v) = true :=
    PEqualNP.Outside.L_meta_1599.graphFun_empty_adj G huv
  have hcirc : circuitFun n C (pairInput u v) = true := by rw [hfun, hgf]
  have hwv : PEqualNP.Outside.L_meta_1599.wv n C (pairInput u v) C.output = true := hcirc
  by_cases hout : C.output < n
  · exfalso
    have hsingle : circuitFun n C (pairInput ⟨C.output, hout⟩ ⟨C.output, hout⟩) = true := by
      have h1 : circuitFun n C (pairInput ⟨C.output, hout⟩ ⟨C.output, hout⟩) =
          PEqualNP.Outside.L_meta_1599.wv n C
            (pairInput ⟨C.output, hout⟩ ⟨C.output, hout⟩) C.output := rfl
      rw [h1, PEqualNP.Outside.L_meta_1599.wv_input hout]
      simp [pairInput]
    have hfalse : graphFun G ∅ (pairInput ⟨C.output, hout⟩ ⟨C.output, hout⟩) = false :=
      PEqualNP.Outside.L_meta_1599.graphFun_empty_single G ⟨C.output, hout⟩
    rw [← hfun, hsingle] at hfalse
    exact absurd hfalse (by simp)
  · have hlen : C.output < n + C.gates.length := by
      by_contra hge
      push_neg at hge
      have hle : (PEqualNP.Outside.L_meta_1599.wiresFrom C.gates
          (List.ofFn (pairInput u v))).length ≤ C.output := by
        rw [PEqualNP.Outside.L_meta_1599.length_wiresFrom]
        simp only [List.length_ofFn]
        omega
      have hzero : PEqualNP.Outside.L_meta_1599.wv n C (pairInput u v) C.output = false := by
        unfold PEqualNP.Outside.L_meta_1599.wv
        rw [List.getD_eq_default _ _ hle]
      rw [hzero] at hwv
      exact absurd hwv (by simp)
    obtain ⟨k, hk⟩ : ∃ k, C.output = n + k := ⟨C.output - n, by omega⟩
    have hklen : k < C.gates.length := by omega
    have hktrue : gateVal n C k (pairInput u v) = true := by
      rw [PEqualNP.Outside.L_meta_1599.gateVal_eq_wv, ← hk]
      exact hwv
    rcases PEqualNP.Outside.L_meta_1599.descent C handor u v k hklen hktrue with
      ⟨i, hile, hiand, hitrue⟩ | ⟨w, hxw, hkw⟩
    · have hex : ∃ i, i ≤ k ∧ (gateAt C i).op = GateOp.and ∧
          gateVal n C i (pairInput u v) = true := ⟨i, hile, hiand, hitrue⟩
      have hspec := Nat.find_spec hex
      refine ⟨Nat.find hex, by omega, ?_⟩
      refine ⟨by omega, hspec.2.1, hspec.2.2, ?_⟩
      intro j hj _ hja
      by_cases hjt : gateVal n C j (pairInput u v) = true
      · exfalso
        exact Nat.find_min hex hj ⟨by omega, hja, hjt⟩
      · cases hv : gateVal n C j (pairInput u v) with
        | true => exact absurd hv hjt
        | false => rfl
    · exfalso
      have hcirc2 : circuitFun n C (pairInput w w) = true := by
        have h1 : circuitFun n C (pairInput w w) =
            PEqualNP.Outside.L_meta_1599.wv n C (pairInput w w) C.output := rfl
        rw [h1, hk, ← PEqualNP.Outside.L_meta_1599.gateVal_eq_wv]
        exact hkw
      have hfalse : graphFun G ∅ (pairInput w w) = false :=
        PEqualNP.Outside.L_meta_1599.graphFun_empty_single G w
      rw [← hfun, hcirc2] at hfalse
      exact absurd hfalse (by simp)
