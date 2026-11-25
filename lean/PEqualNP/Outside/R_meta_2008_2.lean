import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2008_2
  (hPlane :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      100 < q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      (∀ p : Fin N, Fintype.card {l : Fin N // I p l} = q + 1) ∧
      (∀ l m : Fin N, l ≠ m → ∃! p : Fin N, I p l ∧ I p m))
  (hPure :
    ∀ (N : ℕ) (C : Circuit) (X : Finset ℕ),
      Monotone2 C →
      (∀ j g, C.gates[j]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + j) →
      (∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∉ X →
        ¬ ((∀ w ∈ g.inputs, ∃ x : Fin N → Bool,
              (C.wires (List.ofFn x ++ List.replicate N false)).getD w false ≠
              (C.wires (List.ofFn x ++ List.replicate N true)).getD w false) ∨
           (∀ w ∈ g.inputs, ∃ y : Fin N → Bool,
              (C.wires (List.replicate N false ++ List.ofFn y)).getD w false ≠
              (C.wires (List.replicate N true ++ List.ofFn y)).getD w false))) →
      let W := fun (w : ℕ) (x y : Fin N → Bool) => (C.wires (List.ofFn x ++ List.ofFn y)).getD w false
      ∀ j g a b, C.gates[j]? = some g → g.op = GateOp.and → g.inputs = [a, b] → j ∉ X →
        ((∀ x y z, W a x y = W a x z) ∧ (∀ x z y, W b x y = W b z y)) ∨
        ((∀ x z y, W a x y = W a z y) ∧ (∀ x y z, W b x y = W b x z)))
  (hCore :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      100 < q → N = q ^ 2 + q + 1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p, Fintype.card {l : Fin N // I p l} = q + 1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      (∀ l m, l ≠ m → ∃! p, I p l ∧ I p m) →
      Monotone2 C →
      (∀ j g, C.gates[j]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + j) →
      let W := fun (w : ℕ) (x y : Fin N → Bool) => (C.wires (List.ofFn x ++ List.ofFn y)).getD w false
      (∀ p l, I p l → W C.output (fun u => decide (u = p)) (fun v => decide (v = l)) = true) →
      (∀ L : Fin N → Bool, Fintype.card {l : Fin N // L l = true} ≤ q →
        W C.output (fun p => decide (¬ ∃ l, I p l ∧ L l = true)) L = false) →
      ∀ X : Finset ℕ,
        (∀ j g a b, C.gates[j]? = some g → g.op = GateOp.and → g.inputs = [a, b] → j ∉ X →
          ((∀ x y z, W a x y = W a x z) ∧ (∀ x z y, W b x y = W b z y)) ∨
          ((∀ x z y, W a x y = W a z y) ∧ (∀ x y z, W b x y = W b x z))) →
        100 * X.card < N * q → N * q ≤ 100 * C.size) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → ∀ (x15 : Finset ℕ), (∀ (x16 : ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x16]? = Option.some x17 → x17.op = PEqualNP.CircuitLowerBounds.GateOp.and → x16 ∉ x15 → ¬((∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.false)).getD x21 Bool.false ≠ (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.true)).getD x21 Bool.false) ∨ ∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.replicate x2 Bool.false ++ List.ofFn x23)).getD x21 Bool.false ≠ (x5.wires (List.replicate x2 Bool.true ++ List.ofFn x23)).getD x21 Bool.false)) → (100 : ℕ) * x15.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q N I inst C hq hN hline hjoin hmono _ hgates hacc hsound X hX hbudget
  obtain ⟨hpt, hmeet⟩ := hPlane q N I hq hN hline hjoin
  have hpure := hPure N C X hmono hgates hX
  have hcf : ∀ (x y : Fin N → Bool),
      (C.wires (List.ofFn x ++ List.ofFn y)).getD C.output false =
      circuitFun (N + N) C (Fin.append x y) := by
    intro x y
    have hof : List.ofFn (Fin.append x y) = List.ofFn x ++ List.ofFn y := by
      rw [List.ofFn_add]
      congr 1
      · apply congrArg List.ofFn; funext i; exact Fin.append_left x y i
      · apply congrArg List.ofFn; funext i; exact Fin.append_right x y i
    change (C.wires (List.ofFn x ++ List.ofFn y)).getD C.output false =
      (C.wires (List.ofFn (Fin.append x y))).getD C.output false
    rw [hof]
  refine hCore q N I C hq hN hline hpt hjoin hmeet hmono hgates ?_ ?_ X hpure hbudget
  · intro p l hI
    dsimp only
    rw [hcf]
    have hx : Fin.append (fun u => decide (u = p)) (fun v => decide (v = l)) =
        (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) := by
      funext k
      refine Fin.addCases (fun a => ?_) (fun b => ?_) k
      · have hne : Fin.castAdd N a ≠ Fin.natAdd N l := by
          intro e
          have hv := congrArg Fin.val e
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          omega
        simp only [Fin.append_left, hne, or_false, Fin.castAdd_inj]
      · have hne : Fin.natAdd N b ≠ Fin.castAdd N p := by
          intro e
          have hv := congrArg Fin.val e
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          omega
        have hiff : Fin.natAdd N b = Fin.natAdd N l ↔ b = l := by
          constructor
          · intro e
            apply Fin.ext
            have hv := congrArg Fin.val e
            simp only [Fin.val_natAdd] at hv
            omega
          · rintro rfl
            rfl
        simp only [Fin.append_right, hne, false_or, hiff]
    rw [hx]
    exact hacc p l hI
  · intro L hL
    dsimp only
    rw [hcf]
    apply hsound (Fin.append (fun p => decide (¬ ∃ l, I p l ∧ L l = true)) L)
    · simpa only [Fin.append_right] using hL
    · rintro ⟨p, l, hI, hp, hl⟩
      rw [Fin.append_left] at hp
      rw [Fin.append_right] at hl
      exact (of_decide_eq_true hp) ⟨l, hI, hl⟩
