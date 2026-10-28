import ThLean.BP.S5.Structure

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S563
open ThresholdFoundations
open ThLean.BP.S5

theorem S5_03Statement_of_deps
    (h01 : ThLean.BP.S5.S5_01Statement) :
    ThLean.BP.S5.S5_03Statement := by
  intro V _ q hq G hG a b hab hFrozen xs hRebuild
  rcases hFrozen with ⟨hGColorable, hFreeze⟩
  have hDeletion := h01 V q hq G hG a
  have hColoring := hDeletion.2 xs hRebuild
  obtain ⟨τ₀, hτ₀⟩ := hGColorable
  have hOutsideColorable : Colorable q (outsideGraph G a) := by
    exact ⟨fun v => τ₀ v.val, (hColoring τ₀).mp hτ₀ |>.1⟩
  have hPalette : ∀ σ, IsColoring q (outsideGraph G a) σ →
      q - 1 ≤ (xs.map σ).toFinset.card := by
    intro σ hσ
    by_contra hBound
    let C : Finset (Fin q) := (xs.map σ).toFinset
    have hCsmall : C.card < q - 1 := by
      simpa [C] using (Nat.lt_of_not_ge hBound)
    have hCsub : C ⊆ Finset.univ := Finset.subset_univ _
    have hAbsent : 2 ≤ (Finset.univ \ C).card := by
      rw [Finset.card_sdiff_of_subset hCsub]
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ \ C).card)
    have hcAbsent : c ∉ C := (Finset.mem_sdiff.mp hc).2
    have hdAbsent : d ∉ C := (Finset.mem_sdiff.mp hd).2
    let τc : V → Fin q := fun v => if hv : v = a then c else σ ⟨v, hv⟩
    let τd : V → Fin q := fun v => if hv : v = a then d else σ ⟨v, hv⟩
    have hτcOutside (v : Outside a) : τc v.val = σ v := by
      simp [τc, v.property]
    have hτdOutside (v : Outside a) : τd v.val = σ v := by
      simp [τd, v.property]
    have hMapC : xs.map (fun v => τc v.val) = xs.map σ :=
      List.map_congr_left (fun v _ => hτcOutside v)
    have hMapD : xs.map (fun v => τd v.val) = xs.map σ :=
      List.map_congr_left (fun v _ => hτdOutside v)
    have hτcColor : IsColoring q G τc := by
      apply (hColoring τc).2
      refine ⟨?_, ?_⟩
      · simpa only [hτcOutside] using hσ
      · rw [hMapC]
        change τc a ∉ C
        rw [show τc a = c by simp [τc]]
        exact hcAbsent
    have hτdColor : IsColoring q G τd := by
      apply (hColoring τd).2
      refine ⟨?_, ?_⟩
      · simpa only [hτdOutside] using hσ
      · rw [hMapD]
        change τd a ∉ C
        rw [show τd a = d by simp [τd]]
        exact hdAbsent
    have hEqC : c = σ ⟨b, Ne.symm hab⟩ := by
      calc
        c = τc a := by simp [τc]
        _ = τc b := hFreeze τc hτcColor
        _ = σ ⟨b, Ne.symm hab⟩ := by simp [τc, Ne.symm hab]
    have hEqD : d = σ ⟨b, Ne.symm hab⟩ := by
      calc
        d = τd a := by simp [τd]
        _ = τd b := hFreeze τd hτdColor
        _ = σ ⟨b, Ne.symm hab⟩ := by simp [τd, Ne.symm hab]
    exact hcd (hEqC.trans hEqD.symm)
  have hNever : neverMonochromatic q (outsideGraph G a) xs := by
    refine ⟨hOutsideColorable, ?_⟩
    intro σ hσ
    have hCard := hPalette σ hσ
    have hTwo : 2 ≤ q - 1 := by omega
    exact hTwo.trans hCard
  have hOutsideColorable' := hOutsideColorable
  obtain ⟨σ₀, hσ₀⟩ := hOutsideColorable
  have hLength : 2 ≤ xs.length := by
    have hCard := hPalette σ₀ hσ₀
    have hCardLength : (xs.map σ₀).toFinset.card ≤ xs.length := by
      simpa using (List.toFinset_card_le (xs.map σ₀))
    exact (Nat.le_trans (by omega : 2 ≤ q - 1) hCard).trans hCardLength
  exact ⟨hOutsideColorable', hPalette, hNever, hLength⟩

example (h01 : ThLean.BP.S5.S5_01Statement) :
    ThLean.BP.S5.S5_03Statement :=
  S5_03Statement_of_deps h01

end ThLean.W.S563
