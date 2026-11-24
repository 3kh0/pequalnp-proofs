import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3497

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def runW (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma runW_nil (x : List Bool) : runW [] x = x := rfl

lemma runW_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    runW (gs ++ [g]) x =
      runW gs x ++ [g.op.eval (g.inputs.map fun i => (runW gs x).getD i false)] := by
  simp [runW]

lemma runW_len (gs : List Gate) (x : List Bool) :
    (runW gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [runW]
  | append_singleton gs g ih =>
    rw [runW_snoc, List.length_append, List.length_singleton, ih, List.length_append, List.length_singleton]
    omega

lemma runW_prefix_getD (g1 g2 : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + g1.length) :
    (runW (g1 ++ g2) x).getD i false = (runW g1 x).getD i false := by
  induction g2 using List.reverseRecOn with
  | nil => simp
  | append_singleton g2 g ih =>
    rw [← List.append_assoc, runW_snoc, List.getD_eq_getElem?_getD, List.getElem?_append_left]
    · rw [← List.getD_eq_getElem?_getD]; exact ih
    · rw [runW_len, List.length_append]; omega

lemma runW_gate_getD (gs : List Gate) (x : List Bool) (k : ℕ) (hk : k < gs.length) :
    (runW gs x).getD (x.length + k) false =
      (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i => (runW (gs.take k) x).getD i false) := by
  have hsplit : gs = gs.take k ++ [gs[k]'hk] ++ gs.drop (k + 1) := by
    rw [List.append_assoc, List.singleton_append, List.getElem_cons_drop, List.take_append_drop]
  conv_lhs => rw [hsplit]
  have hlenk : (gs.take k).length = k := List.length_take_of_le hk.le
  rw [runW_prefix_getD (gs.take k ++ [gs[k]'hk]) (gs.drop (k + 1)) x (x.length + k) (by simp; omega)]
  rw [runW_snoc]
  have hlenw : (runW (gs.take k) x).length = x.length + k := by rw [runW_len, hlenk]
  rw [← hlenw, List.getD_eq_getElem?_getD, List.getElem?_concat_length]
  rfl

def cnfRec (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Finset (Fin n)) :=
  if hw : w < n then
    {{⟨w, hw⟩}}
  else if hk : w - n < C.gates.length then
    let g := C.gates[w - n]'hk
    match g.inputs with
    | [a, b] =>
      if hab : a < w ∧ b < w then
        if g.op.eval [false, true] = true then
          (cnfRec n C a).biUnion fun c1 => (cnfRec n C b).image fun c2 => c1 ∪ c2
        else
          cnfRec n C a ∪ cnfRec n C b
      else
        {∅}
    | _ => {∅}
  else
    {∅}

lemma cnfRec_lt (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    cnfRec n C w = {{⟨w, hw⟩}} := by
  rw [cnfRec]
  simp [hw]

lemma cnfRec_ge (n : ℕ) (C : Circuit) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    cnfRec n C w = {∅} := by
  rw [cnfRec]
  have h1 : ¬ w < n := by omega
  have h2 : ¬ w - n < C.gates.length := by omega
  simp [h1, h2]

lemma cnfRec_gate (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (a b : ℕ) (hin : (C.gates[k]'hk).inputs = [a, b]) (ha : a < n + k) (hb : b < n + k) :
    cnfRec n C (n + k) =
      if (C.gates[k]'hk).op.eval [false, true] = true then
        (cnfRec n C a).biUnion fun c1 => (cnfRec n C b).image fun c2 => c1 ∪ c2
      else
        cnfRec n C a ∪ cnfRec n C b := by
  conv_lhs => rw [cnfRec]
  have h1 : ¬ n + k < n := by omega
  have hsub : n + k - n = k := Nat.add_sub_cancel_left n k
  have h2 : n + k - n < C.gates.length := by omega
  simp only [h1, ↓reduceDIte, h2]
  have hg : C.gates[n + k - n]'h2 = C.gates[k]'hk := by
    congr 1
  simp only [hg, hin, ha, hb, and_self, ↓reduceDIte]

lemma eval_cnf (n : ℕ) (C : Circuit) (hmono : Monotone2 C)
    (hwf : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < n + k)
    (x : List Bool) (hx : x.length = n) :
    ∀ w : ℕ, (C.wires x).getD w false = true ↔
      ∀ c ∈ cnfRec n C w, ∃ i ∈ c, x.getD (↑i) false = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    by_cases hwn : w < n
    · rw [cnfRec_lt n C w hwn]
      have hpr := runW_prefix_getD [] C.gates x w (by simp [hx]; omega)
      change (runW ([] ++ C.gates) x).getD w false = true ↔ _
      rw [hpr, runW_nil]
      simp
    · by_cases hwg : w < n + C.gates.length
      · let k := w - n
        have hwk : w = n + k := by omega
        have hk : k < C.gates.length := by omega
        have hsome : C.gates[k]? = some (C.gates[k]'hk) := List.getElem?_eq_getElem hk
        obtain ⟨a, b, hin, hab, hbk⟩ := hwf k (C.gates[k]'hk) hsome
        have hak : a < n + k := by omega
        rw [hwk, cnfRec_gate n C k hk a b hin hak hbk]
        have hgate := runW_gate_getD C.gates x k hk
        rw [hx] at hgate
        change (runW C.gates x).getD (n + k) false = true ↔ _
        rw [hgate, hin]
        have ha_pre : (runW (C.gates.take k) x).getD a false = (C.wires x).getD a false := by
          have hlenk : (C.gates.take k).length = k := List.length_take_of_le hk.le
          have hpr := runW_prefix_getD (C.gates.take k) (C.gates.drop k) x a (by rw [hx, hlenk]; exact hak)
          rw [List.take_append_drop] at hpr
          exact hpr.symm
        have hb_pre : (runW (C.gates.take k) x).getD b false = (C.wires x).getD b false := by
          have hlenk : (C.gates.take k).length = k := List.length_take_of_le hk.le
          have hpr := runW_prefix_getD (C.gates.take k) (C.gates.drop k) x b (by rw [hx, hlenk]; exact hbk)
          rw [List.take_append_drop] at hpr
          exact hpr.symm
        have iha := ih a (by omega)
        have ihb := ih b (by omega)
        have hmem : C.gates[k]'hk ∈ C.gates := List.getElem_mem hk
        have hop := (hmono (C.gates[k]'hk) hmem).1
        rcases hop with hop | hop
        · rw [hop]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.and_true, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
            ha_pre, hb_pre, iha, ihb]
          constructor
          · rintro ⟨ha', hb'⟩ c hc
            rcases Finset.mem_union.mp hc with hc | hc
            · exact ha' c hc
            · exact hb' c hc
          · intro hall
            exact ⟨fun c hc => hall c (Finset.mem_union_left _ hc),
              fun c hc => hall c (Finset.mem_union_right _ hc)⟩
        · rw [hop]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            id_eq, Bool.or_false, Bool.false_or, ↓reduceIte, Bool.or_eq_true,
            ha_pre, hb_pre, iha, ihb]
          constructor
          · intro hor c hc
            rcases Finset.mem_biUnion.mp hc with ⟨c1, hc1, hc2⟩
            rcases Finset.mem_image.mp hc2 with ⟨c2, hc2', rfl⟩
            rcases hor with ha' | hb'
            · obtain ⟨i, hi, hx'⟩ := ha' c1 hc1
              exact ⟨i, Finset.mem_union_left _ hi, hx'⟩
            · obtain ⟨i, hi, hx'⟩ := hb' c2 hc2'
              exact ⟨i, Finset.mem_union_right _ hi, hx'⟩
          · intro hall
            by_cases ha' : ∀ c ∈ cnfRec n C a, ∃ i ∈ c, x.getD (↑i) false = true
            · exact Or.inl ha'
            · right
              push Not at ha'
              obtain ⟨c1, hc1, hbad⟩ := ha'
              intro c2 hc2
              have hmemU : c1 ∪ c2 ∈ (cnfRec n C a).biUnion fun c1 => (cnfRec n C b).image fun c2 => c1 ∪ c2 :=
                Finset.mem_biUnion.mpr ⟨c1, hc1, Finset.mem_image.mpr ⟨c2, hc2, rfl⟩⟩
              obtain ⟨i, hi, hx'⟩ := hall (c1 ∪ c2) hmemU
              rcases Finset.mem_union.mp hi with hi1 | hi2
              · exact absurd hx' (hbad i hi1)
              · exact ⟨i, hi2, hx'⟩
      · have hge : n + C.gates.length ≤ w := by omega
        rw [cnfRec_ge n C w hge]
        have hlen : (C.wires x).length ≤ w := by
          change (runW C.gates x).length ≤ w
          rw [runW_len, hx]; exact hge
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]
        simp

end PEqualNP.Outside.L_meta_3497

theorem PEqualNP.Outside.L_meta_3497 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x4]? = Option.some x5 → ∃ (x7 : ℕ) (x8 : ℕ), x5.inputs = [x7, x8] ∧ x7 < x8 ∧ x8 < x1 + x4) → ∃ (x5 : ℕ → Finset (Finset (Fin x1))), (∀ (x6 : Fin x1), x5 ↑x6 = {{x6}}) ∧ (∀ (x6 : ℕ) (x7 : x6 < x2.size), ∃ (x8 : ℕ) (x9 : ℕ), x2.gates[x6].inputs = [x8, x9] ∧ x8 < x9 ∧ x9 < x1 + x6 ∧ x5 (x1 + x6) = if x2.gates[x6].op.eval [Bool.false, Bool.true] = Bool.true then (x5 x8).biUnion fun (x10 : Finset (Fin x1)) => Finset.image (fun (x11 : Finset (Fin x1)) => x10 ∪ x11) (x5 x9) else x5 x8 ∪ x5 x9) ∧ ∀ (x6 : List Bool), x6.length = x1 → ∀ (x8 : ℕ), (x2.wires x6).getD x8 Bool.false = Bool.true ↔ ∀ x9 ∈ x5 x8, ∃ x11 ∈ x9, x6.getD (↑x11) Bool.false = Bool.true := by
  intro n C hmono hwf
  refine ⟨PEqualNP.Outside.L_meta_3497.cnfRec n C, ?_, ?_, ?_⟩
  · intro i
    exact PEqualNP.Outside.L_meta_3497.cnfRec_lt n C i.val i.isLt
  · intro k hk
    have hsome : C.gates[k]? = some (C.gates[k]'hk) := List.getElem?_eq_getElem hk
    obtain ⟨a, b, hin, hab, hbk⟩ := hwf k (C.gates[k]'hk) hsome
    refine ⟨a, b, hin, hab, hbk, ?_⟩
    exact PEqualNP.Outside.L_meta_3497.cnfRec_gate n C k hk a b hin (by omega) hbk
  · intro x hx w
    exact PEqualNP.Outside.L_meta_3497.eval_cnf n C hmono hwf x hx w
