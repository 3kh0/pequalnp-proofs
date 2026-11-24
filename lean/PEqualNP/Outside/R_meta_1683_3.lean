import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1683_3
    (assemble :
      let aff (x : Fin 26 → Bool) (i : Fin 21) : Bool :=
        x (Fin.ofNat 26 (if i.val = 0 then 2 else if i.val < 6 then i.val + 3 else if i.val < 9 then i.val + 4 else i.val + 5))
      let near (p w : Fin 13) : Prop := ∃ d ∈ ([0, 1, 3, 9] : List (Fin 13)), p = w + d
      ∀ D : Circuit, Monotone2 D → ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size + 20 ∧
        ∀ x : Fin 26 → Bool, circuitFun 26 C x =
          (decide (∃ p w : Fin 13, p ∈ ([0, 1, 3, 9] : List (Fin 13)) ∧ near p w ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true) ||
          circuitFun 21 D (aff x)))
    (search :
      let aff (x : Fin 26 → Bool) (i : Fin 21) : Bool :=
        x (Fin.ofNat 26 (if i.val = 0 then 2 else if i.val < 6 then i.val + 3 else if i.val < 9 then i.val + 4 else i.val + 5))
      let near (p w : Fin 13) : Prop := ∃ d ∈ ([0, 1, 3, 9] : List (Fin 13)), p = w + d
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 43 ∧
        (∀ p w : Fin 13, p ∉ ([0, 1, 3, 9] : List (Fin 13)) → near p w →
          circuitFun 21 D (aff (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w))) = true) ∧
        (∀ x : Fin 26 → Bool,
          (∀ p w : Fin 13, p ∉ ([0, 1, 3, 9] : List (Fin 13)) → w ≠ 0 →
            x (Fin.castAdd 13 p) = true → x (Fin.natAdd 13 w) = true → ¬ near p w) →
          ((∃ w3 : Fin 13, ∀ p : Fin 13, p ∉ ([0, 1, 3, 9] : List (Fin 13)) →
              x (Fin.castAdd 13 p) = true → near p w3) ∨
           (∃ v4 : Fin 13, ∀ w : Fin 13, w ≠ 0 →
              x (Fin.natAdd 13 w) = true → near v4 w)) →
          circuitFun 21 D (aff x) = false)) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false) := by
  have incidence : ∀ p w : Fin 13,
      (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) ↔
      (∃ d ∈ ([0, 1, 3, 9] : List (Fin 13)), p = w + d) := by decide +kernel
  obtain ⟨D, hD, sizeD, posD, negD⟩ := search
  obtain ⟨C, hC, sizeC, specC⟩ := assemble D hD
  refine ⟨C, hC, by omega, ?_, ?_⟩
  · intro p w hi
    change circuitFun 26 C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true
    rw [specC]
    by_cases hp : p ∈ ([0, 1, 3, 9] : List (Fin 13))
    · apply Bool.or_eq_true_iff.mpr
      left
      exact decide_eq_true ⟨p, w, hp, (incidence p w).mp hi, by simp, by simp⟩
    · rw [posD p w hp ((incidence p w).mp hi), Bool.or_true]
  · intro P _ hdeg
    let z : Fin 26 → Bool := fun kk =>
      decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨
        (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧
          (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))
    change circuitFun 26 C z = false
    have cross (p w : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 w := by
      intro h
      have hv := congrArg Fin.val h
      change p.val = 13 + w.val at hv
      have hp := p.isLt
      omega
    have leftbit (p : Fin 13) : z (Fin.castAdd 13 p) = true ↔ p ∈ P := by
      simp only [z, decide_eq_true_eq, cross, false_and, exists_false, or_false]
      constructor
      · rintro ⟨q, hq, heq⟩
        have eqp : p = q := Fin.ext (congrArg (fun k : Fin 26 => k.val) heq)
        exact eqp ▸ hq
      · intro hp
        exact ⟨p, hp, rfl⟩
    have rightbit (w : Fin 13) :
        z (Fin.natAdd 13 w) = true ↔
          (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w + dd)) := by
      have cross' (p : Fin 13) : Fin.natAdd 13 w ≠ Fin.castAdd 13 p := fun h => cross p w h.symm
      simp only [z, decide_eq_true_eq, cross', and_false, exists_false, false_or]
      constructor
      · rintro ⟨v, hv, hmiss⟩
        have eqv : w = v := Fin.ext (by
          have hval := congrArg Fin.val hv
          change 13 + w.val = 13 + v.val at hval
          omega)
        exact eqv.symm ▸ hmiss
      · intro hmiss
        exact ⟨w, rfl, hmiss⟩
    have miss (p w : Fin 13) (hp : z (Fin.castAdd 13 p) = true) (hw : z (Fin.natAdd 13 w) = true) :
        ¬ (∃ d ∈ ([0, 1, 3, 9] : List (Fin 13)), p = w + d) := fun h =>
      (rightbit w).mp hw p ((leftbit p).mp hp) ((incidence p w).mpr h)
    have noLine0 :
        ¬ ∃ p w : Fin 13, p ∈ ([0, 1, 3, 9] : List (Fin 13)) ∧
          (∃ d ∈ ([0, 1, 3, 9] : List (Fin 13)), p = w + d) ∧
          z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 w) = true := by
      rintro ⟨p, w, _, hi, hp, hw⟩
      exact miss p w hp hw hi
    have hDfalse :
        circuitFun 21 D
          (fun i : Fin 21 =>
            z (Fin.ofNat 26 (if i.val = 0 then 2 else if i.val < 6 then i.val + 3 else if i.val < 9 then i.val + 4 else i.val + 5))) = false := by
      apply negD z (fun p w _ _ hp hw => miss p w hp hw)
      rcases hdeg with ⟨w3, hw3⟩ | ⟨v4, hv4⟩
      · exact Or.inl ⟨w3, fun p _ hp => (incidence p w3).mp (hw3 p ((leftbit p).mp hp))⟩
      · exact Or.inr ⟨v4, fun w _ hw => (incidence v4 w).mp (hv4 w ((rightbit w).mp hw))⟩
    rw [specC, decide_eq_false noLine0, hDfalse]
    rfl
