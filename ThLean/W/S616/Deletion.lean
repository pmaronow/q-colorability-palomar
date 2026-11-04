module

public import ThLean.BP.S6.Deletion

@[expose] public section

noncomputable section
open scoped BigOperators
open ThresholdFoundations
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S616

private abbrev Edge (n : ℕ) := ThLean.BP.S6.Edge n

private def edgeOf {n : ℕ} (a b : Fin n) (hab : a ≠ b) : Edge n :=
  ⟨s(a, b), by
    intro v hv
    have h := Sym2.eq_iff.mp hv
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact hab (ha.trans hb.symm)
    · exact hab (ha.trans hb.symm)⟩

private lemma sum_indicator_card {α : Type*} [Fintype α] (P : α → Prop) :
    (∑ x : α, indicator (P x)) = (Finset.univ.filter P).card := by
  classical
  simp [indicator]

private lemma touches_sym2_pair {n : ℕ} (a b c : Fin n) :
    Touches c (s(a, b)) ↔ c = a ∨ c = b := by
  constructor
  · rintro ⟨v, hv⟩
    rcases Sym2.eq_iff.mp hv with ⟨hca, hvb⟩ | ⟨hva, hcb⟩
    · exact Or.inl hca.symm
    · exact Or.inr hcb.symm
  · rintro (rfl | rfl)
    · exact ⟨b, rfl⟩
    · exact ⟨a, Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)⟩

private lemma pivotalDeletionCount_edgeOf
    (h13 : ThLean.BP.S6.S6_13Statement)
    (n q j : ℕ) (hn : 3 ≤ n) (hq : 3 ≤ q) (G : ThLean.BP.S6.Graph n)
    (a b : Fin n) (hab : a ≠ b) :
    pivotalDeletionCount q j G (edgeOf a b hab) =
      indicator (degree G a = j - 1) * (relationSection q G a b).card +
      indicator (degree G b = j - 1) * (relationSection q G b a).card := by
  classical
  let e := edgeOf a b hab
  have hnewA : (Finset.univ.filter (fun v : Fin n =>
      a ≠ v ∧ Frozen q (addPair G e) a v ∧ ¬ Frozen q G a v)).card =
      (relationSection q G a b).card := by
    exact h13 n q hn hq G a b e hab rfl
  have hnewB : (Finset.univ.filter (fun v : Fin n =>
      b ≠ v ∧ Frozen q (addPair G e) b v ∧ ¬ Frozen q G b v)).card =
      (relationSection q G b a).card := by
    apply h13 n q hn hq G b a e hab.symm
    change s(a, b) = s(b, a)
    exact Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)
  have hta : Touches a e.val := by
    exact ⟨b, rfl⟩
  have htb : Touches b e.val := by
    exact ⟨a, Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)⟩
  have hterm (c : Fin n) :
      (∑ v : Fin n, indicator (Touches c e.val ∧ c ≠ v ∧
        Frozen q (addPair G e) c v ∧ ¬ Frozen q G c v ∧ degree G c = j - 1)) =
      (if c = a then indicator (degree G a = j - 1) * (relationSection q G a b).card
       else if c = b then indicator (degree G b = j - 1) * (relationSection q G b a).card
       else 0) := by
    by_cases hca : c = a
    · subst c
      by_cases hd : degree G a = j - 1
      · have hs : (∑ v : Fin n, indicator
            (a ≠ v ∧ Frozen q (addPair G e) a v ∧ ¬ Frozen q G a v)) =
          (Finset.univ.filter (fun v : Fin n =>
            a ≠ v ∧ Frozen q (addPair G e) a v ∧ ¬ Frozen q G a v)).card :=
          by simpa using (sum_indicator_card (fun v : Fin n =>
            a ≠ v ∧ Frozen q (addPair G e) a v ∧ ¬ Frozen q G a v))
        calc
          (∑ v : Fin n, indicator (Touches a e.val ∧ a ≠ v ∧
              Frozen q (addPair G e) a v ∧ ¬ Frozen q G a v ∧ degree G a = j - 1))
              = ∑ v : Fin n, indicator
                  (a ≠ v ∧ Frozen q (addPair G e) a v ∧ ¬ Frozen q G a v) := by
                    apply Finset.sum_congr rfl
                    intro v hv
                    simp [hta, hd]
          _ = (Finset.univ.filter (fun v : Fin n =>
                a ≠ v ∧ Frozen q (addPair G e) a v ∧ ¬ Frozen q G a v)).card := hs
          _ = (relationSection q G a b).card := by exact_mod_cast hnewA
          _ = indicator (degree G a = j - 1) * (relationSection q G a b).card := by
                simp [indicator, hd]
          _ = (if a = a then indicator (degree G a = j - 1) *
                (relationSection q G a b).card else if a = b then
                indicator (degree G b = j - 1) * (relationSection q G b a).card else 0) := by
                  simp
      · simp [indicator, hta, hd]
    · by_cases hcb : c = b
      · subst c
        by_cases hd : degree G b = j - 1
        · have hs : (∑ v : Fin n, indicator
              (b ≠ v ∧ Frozen q (addPair G e) b v ∧ ¬ Frozen q G b v)) =
            (Finset.univ.filter (fun v : Fin n =>
              b ≠ v ∧ Frozen q (addPair G e) b v ∧ ¬ Frozen q G b v)).card :=
            by simpa using (sum_indicator_card (fun v : Fin n =>
              b ≠ v ∧ Frozen q (addPair G e) b v ∧ ¬ Frozen q G b v))
          calc
            (∑ v : Fin n, indicator (Touches b e.val ∧ b ≠ v ∧
                Frozen q (addPair G e) b v ∧ ¬ Frozen q G b v ∧ degree G b = j - 1))
                = ∑ v : Fin n, indicator
                    (b ≠ v ∧ Frozen q (addPair G e) b v ∧ ¬ Frozen q G b v) := by
                      apply Finset.sum_congr rfl
                      intro v hv
                      simp [htb, hd]
            _ = (Finset.univ.filter (fun v : Fin n =>
                  b ≠ v ∧ Frozen q (addPair G e) b v ∧ ¬ Frozen q G b v)).card := hs
            _ = (relationSection q G b a).card := by exact_mod_cast hnewB
            _ = indicator (degree G b = j - 1) * (relationSection q G b a).card := by
                  simp [indicator, hd]
            _ = (if b = a then indicator (degree G a = j - 1) *
                  (relationSection q G a b).card else if b = b then
                  indicator (degree G b = j - 1) * (relationSection q G b a).card else 0) := by
                    simp [hab, ne_comm]
        · simp [indicator, htb, hd, hca]
      · have hnot : ¬ Touches c e.val := by
          intro ht
          have ht' : c = a ∨ c = b := by
            apply (touches_sym2_pair a b c).mp
            simpa [e, edgeOf] using ht
          rcases ht' with h | h
          · exact hca h
          · exact hcb h
        simp [indicator, hnot, hca, hcb]
  unfold pivotalDeletionCount
  calc
    (∑ c : Fin n, ∑ v : Fin n, indicator (Touches c e.val ∧ c ≠ v ∧
        Frozen q (addPair G e) c v ∧ ¬ Frozen q G c v ∧ degree G c = j - 1))
        = ∑ c : Fin n, (if c = a then indicator (degree G a = j - 1) *
              (relationSection q G a b).card else if c = b then
              indicator (degree G b = j - 1) * (relationSection q G b a).card else 0) := by
            apply Finset.sum_congr rfl
            intro c hc
            exact hterm c
    _ = indicator (degree G a = j - 1) * (relationSection q G a b).card +
        indicator (degree G b = j - 1) * (relationSection q G b a).card := by
          have hsplit (c : Fin n) :
              (if c = a then indicator (degree G a = j - 1) *
                  (relationSection q G a b).card else if c = b then
                  indicator (degree G b = j - 1) * (relationSection q G b a).card else 0) =
                (if c = a then indicator (degree G a = j - 1) *
                    (relationSection q G a b).card else 0) +
                (if c = b then indicator (degree G b = j - 1) *
                    (relationSection q G b a).card else 0) := by
            by_cases hca : c = a
            · subst c
              simp [hab]
            · by_cases hcb : c = b
              · subst c
                simp [hca]
              · simp [hca, hcb]
          calc
            (∑ c : Fin n, (if c = a then indicator (degree G a = j - 1) *
                (relationSection q G a b).card else if c = b then
                indicator (degree G b = j - 1) * (relationSection q G b a).card else 0)) =
                ∑ c : Fin n, ((if c = a then indicator (degree G a = j - 1) *
                  (relationSection q G a b).card else 0) +
                  (if c = b then indicator (degree G b = j - 1) *
                  (relationSection q G b a).card else 0)) := by
                    apply Finset.sum_congr rfl
                    intro c hc
                    exact hsplit c
            _ = _ := by
              rw [Finset.sum_add_distrib]
              simp [Finset.sum_ite_eq']

private lemma section_sum_eq_relation_card
    (h05 : ThLean.BP.S6.S6_05Statement)
    (n q : ℕ) (hn : 3 ≤ n) (hq : 3 ≤ q) (G : ThLean.BP.S6.Graph n) (a : Fin n) :
    (∑ b : Fin n, indicator (a ≠ b) * (relationSection q G a b).card) =
      (relation q G a).card := by
  classical
  rcases h05 n q hn hq G a with ⟨_, _, _, hdiag, hsum, _, _, _, hnotColorable⟩
  have hdiag' : relationSection q G a a = ∅ := by
    by_cases hc : Colorable q G
    · have ha : a ∈ frozenClass q G a := by
        simp [frozenClass, Frozen, hc]
      exact hdiag a ha
    · have hrel : relation q G a = ∅ := (hnotColorable hc).1
      unfold relationSection
      rw [hrel]
      simp
  have hsumR : (∑ b : Fin n, ((relationSection q G a b).card : ℝ)) =
      ((relation q G a).card : ℝ) := by
    exact_mod_cast hsum.symm
  calc
    (∑ b : Fin n, indicator (a ≠ b) * ((relationSection q G a b).card : ℝ)) =
        (∑ b : Fin n, ((relationSection q G a b).card : ℝ)) := by
          apply Finset.sum_congr rfl
          intro b hb
          by_cases hab : a = b
          · subst b
            simp [indicator, hdiag']
          · simp [indicator, hab]
    _ = (relation q G a).card := hsumR

theorem S6_14Statement_of_deps
    (h03 : ThLean.BP.S6.S6_03Statement)
    (h05 : ThLean.BP.S6.S6_05Statement)
    (h13 : ThLean.BP.S6.S6_13Statement) :
    ThLean.BP.S6.S6_14Statement := by
  classical
  intro n q j hn hq hj G
  rcases h03 n hn with ⟨_, hpairs, _⟩
  let H : Sym2 (Fin n) → ℝ := fun e =>
    if he : ∀ v : Fin n, e ≠ s(v, v) then
      pivotalDeletionCount q j G ⟨e, he⟩
    else 0
  have hmeanSame : uniformMean (fun e : Edge n => H e.val) =
      uniformMean (pivotalDeletionCount q j G) := by
    unfold uniformMean
    congr 1
    apply Finset.sum_congr rfl
    intro e he
    simp [H, e.property]
  have hpairMean := hpairs H
  rw [hmeanSame] at hpairMean
  have hpairRewrite :
      (∑ a : Fin n, ∑ b : Fin n,
        indicator (a ≠ b) * H (s(a, b))) =
      2 * (∑ a : Fin n, indicator (degree G a = j - 1) *
        (relation q G a).card) := by
    have hpoint (a b : Fin n) (hab : a ≠ b) : H (s(a, b)) =
        indicator (degree G a = j - 1) * (relationSection q G a b).card +
        indicator (degree G b = j - 1) * (relationSection q G b a).card := by
      have hnd : ∀ v : Fin n, s(a, b) ≠ s(v, v) := by
        intro v hv
        rcases Sym2.eq_iff.mp hv with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact hab (ha.trans hb.symm)
        · exact hab (ha.trans hb.symm)
      rw [show H (s(a, b)) = pivotalDeletionCount q j G (edgeOf a b hab) by
        simp [H, hnd, edgeOf]]
      exact pivotalDeletionCount_edgeOf h13 n q j hn hq G a b hab
    have hrewrite :
        (∑ a : Fin n, ∑ b : Fin n, indicator (a ≠ b) * H (s(a, b))) =
        ∑ a : Fin n, ∑ b : Fin n, indicator (a ≠ b) *
          (indicator (degree G a = j - 1) * (relationSection q G a b).card +
           indicator (degree G b = j - 1) * (relationSection q G b a).card) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hab : a = b
      · simp [hab, indicator]
      · rw [hpoint a b hab]
    have hmain :
        (∑ a : Fin n, ∑ b : Fin n, indicator (a ≠ b) *
          (indicator (degree G a = j - 1) * (relationSection q G a b).card +
           indicator (degree G b = j - 1) * (relationSection q G b a).card)) =
        2 * (∑ a : Fin n, indicator (degree G a = j - 1) *
          (relation q G a).card) := by
      have hforward :
          (∑ a : Fin n, ∑ b : Fin n, indicator (a ≠ b) *
            (indicator (degree G a = j - 1) * (relationSection q G a b).card)) =
          ∑ a : Fin n, indicator (degree G a = j - 1) * (relation q G a).card := by
        apply Finset.sum_congr rfl
        intro a ha
        calc
          (∑ b : Fin n, indicator (a ≠ b) *
              (indicator (degree G a = j - 1) * (relationSection q G a b).card)) =
              indicator (degree G a = j - 1) *
                (∑ b : Fin n, indicator (a ≠ b) * (relationSection q G a b).card) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro b hb
                  ring
          _ = indicator (degree G a = j - 1) * (relation q G a).card := by
                rw [section_sum_eq_relation_card h05 n q hn hq G a]
      have hback :
          (∑ a : Fin n, ∑ b : Fin n, indicator (a ≠ b) *
            (indicator (degree G b = j - 1) * (relationSection q G b a).card)) =
          ∑ a : Fin n, indicator (degree G a = j - 1) * (relation q G a).card := by
        rw [Finset.sum_comm]
        simpa [ne_comm] using hforward
      calc
        _ = (∑ a : Fin n, ∑ b : Fin n, indicator (a ≠ b) *
              (indicator (degree G a = j - 1) * (relationSection q G a b).card)) +
            (∑ a : Fin n, ∑ b : Fin n, indicator (a ≠ b) *
              (indicator (degree G b = j - 1) * (relationSection q G b a).card)) := by
                simp_rw [mul_add, Finset.sum_add_distrib]
        _ = _ := by rw [hforward, hback]; ring
    exact hrewrite.trans hmain
  have hmeanFormula : uniformMean (pivotalDeletionCount q j G) =
      (2 * (∑ a : Fin n, indicator (degree G a = j - 1) *
        (relation q G a).card)) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    rw [hpairRewrite] at hpairMean
    exact hpairMean
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have hn' : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    linarith
  have hbetaSum : (∑ a : Fin n, indicator (degree G a = j - 1) * beta q G a) =
      (∑ a : Fin n, indicator (degree G a = j - 1) * (relation q G a).card) /
        (n : ℝ) ^ 2 := by
    simp only [beta, Fintype.card_fin]
    simp_rw [div_eq_mul_inv]
    change Finset.univ.sum (fun a : Fin n => indicator (degree G a = j - 1) *
        (((relation q G a).card : ℝ) * ((n : ℝ) ^ 2)⁻¹)) =
      (Finset.univ.sum (fun a : Fin n => indicator (degree G a = j - 1) *
        (relation q G a).card)) * ((n : ℝ) ^ 2)⁻¹
    rw [Finset.sum_mul Finset.univ
      (fun a : Fin n => indicator (degree G a = j - 1) * (relation q G a).card)
      ((n : ℝ) ^ 2)⁻¹]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [hmeanFormula, hbetaSum]
  field_simp [ne_of_gt hn0, ne_of_gt hn1]

end ThLean.W.S616
