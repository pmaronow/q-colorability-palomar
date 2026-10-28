import ThLean.BP.S6.Foundation

noncomputable section
open scoped BigOperators
open ThresholdFoundations
open ThLean.BP.S6
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S605

private abbrev StrictPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

private def edgeEquivStrictPair (n : ℕ) : Edge n ≃ StrictPair n where
  toFun e := by
    let p := Sym2.sortEquiv e.val
    have hp : p.val.1 < p.val.2 := by
      have hne : p.val.1 ≠ p.val.2 := by
        intro heq
        apply e.property p.val.1
        have hs : Sym2.sortEquiv.symm p = e.val :=
          Equiv.symm_apply_apply Sym2.sortEquiv e.val
        simpa [Sym2.sortEquiv_symm_apply, heq] using hs.symm
      exact p.property.lt_of_ne hne
    exact ⟨p.val, hp⟩
  invFun p := by
    refine ⟨s(p.val.1, p.val.2), ?_⟩
    intro v hv
    have h := Sym2.eq_iff.mp hv
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact (ne_of_lt p.property) (h₁.trans h₂.symm)
    · exact (ne_of_lt p.property) (h₁.trans h₂.symm)
  left_inv e := by
    apply Subtype.ext
    simpa only [Sym2.sortEquiv_symm_apply] using
      (Equiv.symm_apply_apply Sym2.sortEquiv e.val)
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact min_eq_left (le_of_lt p.property)
    · exact max_eq_right (le_of_lt p.property)

private def edgeEquivNonDiag (n : ℕ) : Edge n ≃ {x : Sym2 (Fin n) // ¬ x.IsDiag} where
  toFun x := by
    rcases x with ⟨e, he⟩
    refine ⟨e, ?_⟩
    intro hd
    cases e using Sym2.ind with
    | _ a b =>
      have hab : a = b := Sym2.mk_isDiag_iff.mp (by simpa using hd)
      subst b
      exact he a rfl
  invFun x := ⟨x.val, by
    intro v hv
    apply x.property
    rw [hv]
    exact Sym2.diag_isDiag v⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

private theorem edge_card (n : ℕ) : Fintype.card (Edge n) = Nat.choose n 2 := by
  rw [Fintype.card_congr (edgeEquivNonDiag n)]
  simpa using (Sym2.card_subtype_not_diag (α := Fin n))

private theorem sum_edge_eq_strict {n : ℕ} (f : Edge n → ℝ) :
    (∑ e : Edge n, f e) =
      ∑ p : StrictPair n, f ((edgeEquivStrictPair n).symm p) := by
  exact (Equiv.sum_comp (edgeEquivStrictPair n).symm f).symm

private theorem strict_sum_eq_double {n : ℕ} (f : Fin n × Fin n → ℝ) :
    (∑ p : StrictPair n, f p.val) =
      ∑ a : Fin n, ∑ b : Fin n, if a < b then f (a, b) else 0 := by
  classical
  let s : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 < p.2)
  have hs : ∀ x : Fin n × Fin n, x ∈ s ↔ x.1 < x.2 := by
    intro x
    simp [s]
  calc
    (∑ p : StrictPair n, f p.val) = ∑ p ∈ s, f p :=
      (Finset.sum_subtype s hs f).symm
    _ = ∑ p ∈ Finset.univ, if p.1 < p.2 then f p else 0 := by
      simp [s, Finset.sum_filter]
    _ = ∑ a : Fin n, ∑ b : Fin n, if a < b then f (a, b) else 0 := by
      rw [← Finset.univ_product_univ, Finset.sum_product]

private theorem touches_sym2_mk_iff {n : ℕ} (u a b : Fin n) :
    Touches u (s(a, b)) ↔ u = a ∨ u = b := by
  constructor
  · rintro ⟨v, hv⟩
    rcases Sym2.eq_iff.mp hv with ⟨hu, _⟩ | ⟨_, hu⟩
    · exact Or.inl hu.symm
    · exact Or.inr hu.symm
  · rintro (hu | hu)
    · subst u
      exact ⟨b, rfl⟩
    · subst u
      exact ⟨a, (Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩))⟩

private theorem sum_ite_const_filter {α : Type} [Fintype α] (P : α → Prop)
    [DecidablePred P] (c : ℝ) :
    (∑ x : α, if P x then c else 0) =
      ((Finset.univ.filter P).card : ℝ) * c := by
  classical
  rw [← Finset.sum_filter]
  simp [Finset.sum_const, nsmul_eq_mul]

private theorem endpoint_pair_sum {n : ℕ} {hn : 1 ≤ n} (z : Fin n → ℝ) :
    (∑ p : StrictPair n, (fun q : Fin n × Fin n => z q.1 + z q.2) p.val) =
      ((n : ℝ) - 1) * ∑ a : Fin n, z a := by
  classical
  rw [strict_sum_eq_double (fun p : Fin n × Fin n => z p.1 + z p.2)]
  have hsplit :
      (∑ a : Fin n, ∑ b : Fin n, if a < b then z a + z b else 0) =
        (∑ a : Fin n, ∑ b : Fin n, if a < b then z a else 0) +
        (∑ a : Fin n, ∑ b : Fin n, if a < b then z b else 0) := by
    simp_rw [← Finset.sum_add_distrib]
    congr 1
    funext a
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hab : a < b <;> simp [hab]
  rw [hsplit]
  have hfirst (a : Fin n) :
      (∑ b : Fin n, if a < b then z a else 0) =
        ((Finset.Ioi a).card : ℝ) * z a := by
    have hcard : (Finset.univ.filter (fun b : Fin n => a < b)) = Finset.Ioi a := by
      ext b
      simp [Finset.mem_Ioi]
    rw [sum_ite_const_filter, hcard]
  have hsecond :
      (∑ a : Fin n, ∑ b : Fin n, if a < b then z b else 0) =
        ∑ b : Fin n, ((Finset.Iio b).card : ℝ) * z b := by
    calc
      (∑ a : Fin n, ∑ b : Fin n, if a < b then z b else 0) =
          ∑ b : Fin n, ∑ a : Fin n, if a < b then z b else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ b : Fin n, ((Finset.Iio b).card : ℝ) * z b := by
            apply Fintype.sum_congr
            intro b
            have hcard : (Finset.univ.filter (fun a : Fin n => a < b)) = Finset.Iio b := by
              ext a
              simp [Finset.mem_Iio]
            rw [sum_ite_const_filter, hcard]
  rw [show (∑ a : Fin n, ∑ b : Fin n, if a < b then z a else 0) =
      ∑ a : Fin n, ((Finset.Ioi a).card : ℝ) * z a by
        apply Fintype.sum_congr
        intro a
        exact hfirst a]
  rw [hsecond]
  have hcounts (a : Fin n) : (Finset.Ioi a).card + (Finset.Iio a).card = n - 1 := by
    simp only [Fin.card_Ioi, Fin.card_Iio]
    omega
  have hcast (a : Fin n) :
      ((Finset.Ioi a).card : ℝ) + (Finset.Iio a).card = (n : ℝ) - 1 := by
    rw [← Nat.cast_add, hcounts a, Nat.cast_sub hn]
    norm_num
  calc
    (∑ a : Fin n, ((Finset.Ioi a).card : ℝ) * z a) +
        ∑ a : Fin n, ((Finset.Iio a).card : ℝ) * z a
        = ∑ a : Fin n, (((Finset.Ioi a).card : ℝ) + (Finset.Iio a).card) * z a := by
          rw [← Finset.sum_add_distrib]
          apply Fintype.sum_congr
          intro a
          ring
    _ = _ := by
      simp_rw [hcast]
      exact (Finset.mul_sum Finset.univ z ((n : ℝ) - 1)).symm

private theorem ordered_sym2_sum {n : ℕ} (h : Sym2 (Fin n) → ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, indicator (a ≠ b) * h (s(a, b))) =
      2 * ∑ p : StrictPair n, h (s((p.val).1, (p.val).2)) := by
  classical
  have hpoint (a b : Fin n) :
      indicator (a ≠ b) * h (s(a, b)) =
        (if a < b then h (s(a, b)) else 0) +
        (if b < a then h (s(b, a)) else 0) := by
    rcases lt_trichotomy a b with hab | hab | hab
    · have hne : a ≠ b := ne_of_lt hab
      have hnot : ¬ b < a := not_lt_of_ge hab.le
      simp [indicator, hne, hab, hnot]
    · subst b
      simp [indicator]
    · have hsym : s(b, a) = s(a, b) :=
        Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)
      have hne : a ≠ b := ne_of_gt hab
      have hnot : ¬ a < b := not_lt_of_ge hab.le
      simp [indicator, hne, hsym, hab, hnot]
  simp_rw [hpoint, Finset.sum_add_distrib]
  have hswap :
      (∑ a : Fin n, ∑ b : Fin n, if b < a then h (s(b, a)) else 0) =
        ∑ a : Fin n, ∑ b : Fin n, if a < b then h (s(a, b)) else 0 := by
    rw [Finset.sum_comm]
  rw [hswap, ← strict_sum_eq_double (fun p : Fin n × Fin n => h (s(p.1, p.2)))]
  ring

private theorem endpoint_edge_sum {n : ℕ} (hn : 1 ≤ n) (z : Fin n → ℝ) :
    (∑ e : Edge n, ∑ a : Fin n, indicator (Touches a e.val) * z a) =
      ((n : ℝ) - 1) * ∑ a : Fin n, z a := by
  rw [sum_edge_eq_strict]
  have hterm (p : StrictPair n) :
      (∑ a : Fin n,
        indicator (Touches a (s(((p : Fin n × Fin n).1), ((p : Fin n × Fin n).2)))) * z a) =
        (fun q : Fin n × Fin n => z q.1 + z q.2) p.val := by
    rcases p with ⟨⟨x, y⟩, hxy⟩
    have hfilter : (Finset.univ.filter (fun a : Fin n => a = x ∨ a = y)) = {x, y} := by
      ext a
      simp [eq_comm, hxy.ne]
    have hsum : (∑ a : Fin n, if a = x ∨ a = y then z a else 0) = z x + z y := by
      rw [← Finset.sum_filter, hfilter]
      simp [hxy.ne]
    simpa [indicator, touches_sym2_mk_iff] using hsum
  change (∑ p : StrictPair n,
      ∑ a : Fin n,
        indicator (Touches a (s(((p : Fin n × Fin n).1), ((p : Fin n × Fin n).2)))) * z a) =
      ((n : ℝ) - 1) * ∑ a : Fin n, z a
  calc
    (∑ p : StrictPair n,
        ∑ a : Fin n,
          indicator (Touches a (s(((p : Fin n × Fin n).1), ((p : Fin n × Fin n).2)))) * z a) =
        ∑ p : StrictPair n, (fun q : Fin n × Fin n => z q.1 + z q.2) p.val := by
          apply Fintype.sum_congr
          intro p
          exact hterm p
    _ = _ := endpoint_pair_sum (hn := hn) z

private theorem touches_edge_sum {n : ℕ} (hn : 1 ≤ n) (u : Fin n) :
    (∑ e : Edge n, indicator (Touches u e.val)) = (n : ℝ) - 1 := by
  rw [sum_edge_eq_strict]
  let z : Fin n → ℝ := fun a => if a = u then 1 else 0
  have hterm (p : StrictPair n) :
      indicator (Touches u (s(((p : Fin n × Fin n).1), ((p : Fin n × Fin n).2)))) =
        (fun q : Fin n × Fin n => z q.1 + z q.2) p.val := by
    rcases p with ⟨⟨x, y⟩, hxy⟩
    rw [touches_sym2_mk_iff]
    by_cases hux : u = x
    · subst u
      simp [z, indicator, hxy.ne, hxy.ne.symm]
    · by_cases huy : u = y
      · subst u
        simp [z, indicator, hxy.ne, hxy.ne.symm]
      · simp [z, indicator, hux, huy, eq_comm]
  change (∑ p : StrictPair n,
      indicator (Touches u (s(((p : Fin n × Fin n).1), ((p : Fin n × Fin n).2))))) = (n : ℝ) - 1
  calc
    (∑ p : StrictPair n,
        indicator (Touches u (s(((p : Fin n × Fin n).1), ((p : Fin n × Fin n).2))))) =
        ∑ p : StrictPair n, (fun q : Fin n × Fin n => z q.1 + z q.2) p.val := by
          apply Fintype.sum_congr
          intro p
          exact hterm p
    _ = _ := by
      rw [endpoint_pair_sum (hn := hn) z]
      simp [z]

private theorem edge_card_real {n : ℕ} :
    (Fintype.card (Edge n) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  rw [edge_card]
  rw [Nat.cast_choose_two]

theorem S6_03Statement_holds : ThLean.BP.S6.S6_03Statement := by
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hcard : (Fintype.card (Edge n) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 :=
    edge_card_real
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have hnm1R : (n : ℝ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    norm_cast
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro z
    unfold uniformMean
    rw [endpoint_edge_sum hn1 z, hcard]
    field_simp [hnR, hnm1R]
  · intro h
    unfold uniformMean
    have hsum :
        (∑ e : Edge n, h e.val) =
          ∑ p : StrictPair n, h (s(((p : Fin n × Fin n).1), ((p : Fin n × Fin n).2))) := by
      simpa [edgeEquivStrictPair] using
        (sum_edge_eq_strict (fun e : Edge n => h e.val))
    rw [hsum, hcard]
    have hordered := ordered_sym2_sum h
    field_simp [hnR, hnm1R] at hordered ⊢
    nlinarith
  · intro u
    unfold uniformProb uniformMean
    rw [touches_edge_sum hn1 u, hcard]
    field_simp [hnR, hnm1R]

end ThLean.W.S605
