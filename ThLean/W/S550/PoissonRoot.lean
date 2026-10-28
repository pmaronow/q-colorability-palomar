import ThLean.BP.S5.Poisson

set_option maxHeartbeats 1000000

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S550
open ThresholdFoundations ThLean.BP.S5

private lemma uniformMean_abs_le {A : Type} [Fintype A] [Nonempty A]
    (f : A → ℝ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ a, |f a| ≤ C) :
    |uniformMean f| ≤ C := by
  have hcard : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty A›)
  have hlow : -C ≤ uniformMean f := by
    unfold uniformMean
    rw [le_div_iff₀ hcard]
    calc
      -C * (Fintype.card A : ℝ) = ∑ _a : A, -C := by simp [mul_comm]
      _ ≤ ∑ a, f a := Finset.sum_le_sum fun a _ => (abs_le.mp (hf a)).1
  have hhigh : uniformMean f ≤ C := by
    unfold uniformMean
    rw [div_le_iff₀ hcard]
    calc
      (∑ a, f a) ≤ ∑ _a : A, C := Finset.sum_le_sum fun a _ => (abs_le.mp (hf a)).2
      _ = C * (Fintype.card A : ℝ) := by simp [mul_comm]
  exact abs_le.mpr ⟨hlow, hhigh⟩

private lemma uniformMean_range {A : Type} [Fintype A] [Nonempty A]
    (f : A → ℝ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ C) :
    0 ≤ uniformMean f ∧ uniformMean f ≤ C := by
  have habs : ∀ a, |f a| ≤ C := fun a =>
    abs_le.mpr ⟨le_trans (neg_nonpos.mpr hC) (hf a).1, (hf a).2⟩
  have hmean := uniformMean_abs_le f C hC habs
  have hcard : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty A›)
  have hlow : 0 ≤ uniformMean f := by
    unfold uniformMean
    exact div_nonneg (Finset.sum_nonneg fun a _ => (hf a).1) (le_of_lt hcard)
  exact ⟨hlow, le_trans (le_abs_self _) hmean⟩

private lemma uniformMean_add_const {A : Type} [Fintype A] [Nonempty A]
    (f : A → ℝ) (c : ℝ) :
    uniformMean (fun a => f a + c) = uniformMean f + c := by
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty A›))
  simp [uniformMean, Finset.sum_add_distrib, div_eq_mul_inv]
  field_simp [hcard]

private lemma uniformMeanENN_ofReal {A : Type} [Fintype A] [Nonempty A]
    (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ENNReal.ofReal (uniformMean f) = uniformMeanENN (fun a => ENNReal.ofReal (f a)) := by
  have hcard : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty A›)
  unfold uniformMean uniformMeanENN
  rw [ENNReal.ofReal_div_of_pos hcard]
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => hf a)]
  simp

private lemma poissonMixture_add_const (hE01 : S5_E01Statement)
    {z : ℝ} (hz : 0 ≤ z) (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ n, |a n| ≤ C) (c : ℝ) :
    poissonMixture z (fun n => a n + c) = poissonMixture z a + c := by
  have hinfo := hE01.1 z hz
  have hw : ∀ n, 0 ≤ poissonWeight z n := fun n => (hinfo.1 n).1
  have hweights := hinfo.2.1
  have hwSumm : Summable (poissonWeight z) := hweights.summable
  have hbaseSumm : Summable (fun n => poissonWeight z n * a n) := by
    apply Summable.of_norm_bounded (g := fun n => poissonWeight z n * C)
      (hwSumm.mul_right C)
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw n)]
    exact mul_le_mul_of_nonneg_left (ha n) (hw n)
  have hconstSumm : Summable (fun n => poissonWeight z n * c) := hwSumm.mul_right c
  unfold poissonMixture
  simp_rw [mul_add]
  rw [hbaseSumm.tsum_add hconstSumm, tsum_mul_right, hweights.tsum_eq]
  simp

private lemma poissonMixture_bounds (hE01 : S5_E01Statement)
    {z : ℝ} (hz : 0 ≤ z) (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ n, |a n| ≤ C) :
    |poissonMixture z a| ≤ C := by
  have hshift : ∀ n, 0 ≤ a n + C ∧ a n + C ≤ 2 * C := by
    intro n
    have h := abs_le.mp (ha n)
    constructor <;> linarith
  have hmixture := (hE01.1 z hz).2.2.2 (2 * C) (fun n => a n + C)
    (by positivity) hshift
  have hlin := poissonMixture_add_const hE01 hz a C hC ha C
  rw [hlin] at hmixture
  exact abs_le.mpr ⟨by linarith [hmixture.2.1], by linarith [hmixture.2.2]⟩

private lemma poissonMixture_range (hE01 : S5_E01Statement)
    {z : ℝ} (hz : 0 ≤ z) (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ C) :
    0 ≤ poissonMixture z a ∧ poissonMixture z a ≤ C := by
  have habs : ∀ n, |a n| ≤ C := fun n =>
    abs_le.mpr ⟨le_trans (neg_nonpos.mpr hC) (ha n).1, (ha n).2⟩
  have habsMean := poissonMixture_bounds hE01 hz a C hC habs
  have hpos : 0 ≤ poissonMixture z a := by
    have hterms : ∀ n, 0 ≤ poissonWeight z n * a n := by
      intro n
      exact mul_nonneg ((hE01.1 z hz).1 n).1 (ha n).1
    exact tsum_nonneg hterms
  exact ⟨hpos, (abs_le.mp habsMean).2⟩

private lemma poissonMixtureENN_ofReal (hE01 : S5_E01Statement)
    {z : ℝ} (hz : 0 ≤ z) (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ C) :
    ENNReal.ofReal (poissonMixture z a) =
      poissonMixtureENN z (fun n => ENNReal.ofReal (a n)) := by
  have hinfo := hE01.1 z hz
  have hsum := (hinfo.2.2.2 C a hC ha).1
  have hnonneg : ∀ n, 0 ≤ poissonWeight z n * a n := by
    intro n
    exact mul_nonneg (hinfo.1 n).1 (ha n).1
  unfold poissonMixture poissonMixtureENN
  rw [ENNReal.ofReal_tsum_of_nonneg hnonneg hsum]
  apply tsum_congr
  intro n
  rw [ENNReal.ofReal_mul (hinfo.1 n).1]

private lemma poissonGraphMean_add_const {V : Type} [Fintype V]
    [Nonempty (Pair V)] (hE01 : S5_E01Statement) {t : ℝ} (ht : 0 ≤ t)
    (f : MGraph V → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ G, |f G| ≤ C) (c : ℝ) :
    poissonGraphMean t (fun G => f G + c) = poissonGraphMean t f + c := by
  let a : ℕ → ℝ := fun k => uniformMean (fun x : EdgeTuple V k => f (tupleGraph x))
  have ha : ∀ k, |a k| ≤ C := by
    intro k
    exact uniformMean_abs_le _ C hC (fun x => hf (tupleGraph x))
  have hfinite : ∀ k,
      uniformMean (fun x : EdgeTuple V k => f (tupleGraph x) + c) = a k + c := by
    intro k
    exact uniformMean_add_const _ c
  unfold poissonGraphMean
  change poissonMixture t (fun k => uniformMean (fun x : EdgeTuple V k => f (tupleGraph x) + c)) =
    poissonMixture t a + c
  have hseq : (fun k => uniformMean (fun x : EdgeTuple V k => f (tupleGraph x) + c)) =
      (fun k => a k + c) := funext hfinite
  rw [hseq]
  exact poissonMixture_add_const hE01 ht a C hC ha c

private lemma poissonGraphMean_range {V : Type} [Fintype V]
    [Nonempty (Pair V)] (hE01 : S5_E01Statement) {t : ℝ} (ht : 0 ≤ t)
    (f : MGraph V → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ G, 0 ≤ f G ∧ f G ≤ C) :
    0 ≤ poissonGraphMean t f ∧ poissonGraphMean t f ≤ C := by
  let a : ℕ → ℝ := fun k => uniformMean (fun x : EdgeTuple V k => f (tupleGraph x))
  have ha : ∀ k, 0 ≤ a k ∧ a k ≤ C := by
    intro k
    exact uniformMean_range _ C hC (fun x => hf (tupleGraph x))
  unfold poissonGraphMean
  exact poissonMixture_range hE01 ht a C hC ha

private lemma poissonGraphMeanENN_ofReal {V : Type} [Fintype V]
    [Nonempty (Pair V)] (hE01 : S5_E01Statement) {t : ℝ} (ht : 0 ≤ t)
    (f : MGraph V → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ G, 0 ≤ f G ∧ f G ≤ C) :
    ENNReal.ofReal (poissonGraphMean t f) =
      poissonGraphMeanENN t (fun G => ENNReal.ofReal (f G)) := by
  let a : ℕ → ℝ := fun k => uniformMean (fun x : EdgeTuple V k => f (tupleGraph x))
  have ha : ∀ k, 0 ≤ a k ∧ a k ≤ C := by
    intro k
    exact uniformMean_range _ C hC (fun x => hf (tupleGraph x))
  have hmix := poissonMixtureENN_ofReal hE01 ht a C hC ha
  have hfinite : ∀ k,
      ENNReal.ofReal (a k) = uniformMeanENN
        (fun x : EdgeTuple V k => ENNReal.ofReal (f (tupleGraph x))) := by
    intro k
    exact uniformMeanENN_ofReal _ (fun x => (hf (tupleGraph x)).1)
  unfold poissonGraphMean poissonGraphMeanENN
  rw [hmix]
  congr 1
  funext k
  exact hfinite k

private lemma listMean_abs_le {V : Type} [Fintype V] [Nonempty V]
    (k : ℕ) (f : List V → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ xs, |f xs| ≤ C) :
    |listMean k f| ≤ C := by
  exact uniformMean_abs_le _ C hC (fun x => hf (List.ofFn x))

private lemma listMean_range {V : Type} [Fintype V] [Nonempty V]
    (k : ℕ) (f : List V → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ xs, 0 ≤ f xs ∧ f xs ≤ C) :
    0 ≤ listMean k f ∧ listMean k f ≤ C := by
  exact uniformMean_range _ C hC (fun x => hf (List.ofFn x))

private lemma listMean_add_const {V : Type} [Fintype V] [Nonempty V]
    (k : ℕ) (f : List V → ℝ) (c : ℝ) :
    listMean k (fun xs => f xs + c) = listMean k f + c := by
  exact uniformMean_add_const _ c

private lemma poissonListMean_add_const {V : Type} [Fintype V] [Nonempty V]
    (hE01 : S5_E01Statement) {z : ℝ} (hz : 0 ≤ z)
    (f : List V → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ xs, |f xs| ≤ C) (c : ℝ) :
    poissonMixture z (fun k => listMean k (fun xs => f xs + c)) =
      poissonMixture z (fun k => listMean k f) + c := by
  have hfinite k := listMean_add_const k f c
  rw [show (fun k => listMean k (fun xs => f xs + c)) =
      (fun k => listMean k f + c) from funext hfinite]
  exact poissonMixture_add_const hE01 hz (fun k => listMean k f) C hC
    (fun k => listMean_abs_le k f C hC hf) c

private lemma poissonListMean_abs_le {V : Type} [Fintype V] [Nonempty V]
    (hE01 : S5_E01Statement) {z : ℝ} (hz : 0 ≤ z)
    (f : List V → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ xs, |f xs| ≤ C) :
    |poissonMixture z (fun k => listMean k f)| ≤ C := by
  apply poissonMixture_bounds hE01 hz _ C hC
  intro k
  exact listMean_abs_le k f C hC hf

private lemma listPoissonMeanENN_ofReal {V : Type} [Fintype V] [Nonempty V]
    (hE01 : S5_E01Statement) {z : ℝ} (hz : 0 ≤ z)
    (f : List V → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ xs, 0 ≤ f xs ∧ f xs ≤ C) :
    ENNReal.ofReal (poissonMixture z (fun k => listMean k f)) =
      uniformPoissonListMeanENN z (fun xs => ENNReal.ofReal (f xs)) := by
  let a : ℕ → ℝ := fun k => listMean k f
  have ha : ∀ k, 0 ≤ a k ∧ a k ≤ C := by
    intro k
    exact listMean_range k f C hC hf
  have hmix := poissonMixtureENN_ofReal hE01 hz a C hC ha
  have hfinite : ∀ k, ENNReal.ofReal (a k) = uniformMeanENN
      (fun x : Fin k → V => ENNReal.ofReal (f (List.ofFn x))) := by
    intro k
    exact uniformMeanENN_ofReal _ (fun x => (hf (List.ofFn x)).1)
  unfold uniformPoissonListMeanENN
  rw [hmix]
  congr 1
  funext k
  exact hfinite k

private lemma ofReal_eq_ofReal_of_nonneg {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h : ENNReal.ofReal x = ENNReal.ofReal y) : x = y := by
  have ht := congrArg ENNReal.toReal h
  simpa [ENNReal.toReal_ofReal hx, ENNReal.toReal_ofReal hy] using ht

private lemma pair_nonempty {V : Type} [Fintype V] (hV : 2 ≤ Fintype.card V) :
    Nonempty (Pair V) := by
  classical
  have hnot : ¬ ∀ a b : V, a = b := by
    intro hall
    have hc : Fintype.card V ≤ 1 := Fintype.card_le_one_iff.mpr hall
    omega
  obtain ⟨a, b, hab⟩ : ∃ a b : V, a ≠ b := by
    by_contra h
    apply hnot
    intro a b
    by_contra hab
    exact h ⟨a, b, hab⟩
  refine ⟨⟨s(a, b), ?_⟩⟩
  intro v hEq
  rcases Sym2.eq_iff.mp hEq with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact hab (ha.trans hb.symm)
  · exact hab (ha.trans hb.symm)

/-- Real bounded test-function form of the one-root Poisson split. -/
theorem S5_09BStatement_of_deps
    (hroot : ThresholdFoundations.PreSplitRootStatement.{0})
    (hE01 : S5_E01Statement) : S5_09BStatement := by
  intro V instV hV t ht f hf
  classical
  obtain ⟨C, hCbound⟩ := hf
  have hC : 0 ≤ C := le_trans (abs_nonneg (f 0)) (hCbound 0)
  letI : Nonempty (Pair V) := pair_nonempty hV
  letI : Nonempty V := (Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V))
  have hOptCard : 2 ≤ Fintype.card (Option V) := by simp; omega
  letI : Nonempty (Pair (Option V)) := pair_nonempty hOptCard
  let n : ℝ := Fintype.card V
  let uRoot : ℝ := ((n - 1) * t) / (n + 1)
  let uLeaf : ℝ := ((n - 1) / (n + 1)) * t
  let z : ℝ := (2 * t) / (n + 1)
  have hn1 : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast (show 1 ≤ Fintype.card V by omega)
  have hden : 0 < n + 1 := by linarith
  have hnsub : 0 ≤ n - 1 := by linarith
  have huRoot : 0 ≤ uRoot := by
    dsimp [uRoot]
    exact div_nonneg (mul_nonneg hnsub ht) (le_of_lt hden)
  have huLeaf : 0 ≤ uLeaf := by
    dsimp [uLeaf]
    exact mul_nonneg (div_nonneg hnsub (le_of_lt hden)) ht
  have hz : 0 ≤ z := by
    dsimp [z]
    exact div_nonneg (mul_nonneg (by norm_num) ht) (le_of_lt hden)
  have huEq : uRoot = uLeaf := by
    dsimp [uRoot, uLeaf]
    field_simp [ne_of_gt hden]
  let g : MGraph (Option V) → ℝ := fun G => f G + C
  have hgRange (G : MGraph (Option V)) : 0 ≤ g G ∧ g G ≤ 2 * C := by
    have h := abs_le.mp (hCbound G)
    constructor <;> dsimp [g] <;> linarith
  have hleftENN := poissonGraphMeanENN_ofReal hE01 ht g (2 * C) (by positivity)
    (fun G => hgRange G)
  let F : MGraph V → ℝ := fun B => poissonMixture z
    (fun j => listMean j (fun xs => g (addRoot B xs)))
  have hinnerRange (B : MGraph V) (j : ℕ) :
      0 ≤ listMean j (fun xs => g (addRoot B xs)) ∧
        listMean j (fun xs => g (addRoot B xs)) ≤ 2 * C := by
    exact listMean_range j _ (2 * C) (by positivity) (fun xs => hgRange (addRoot B xs))
  have hFRange (B : MGraph V) : 0 ≤ F B ∧ F B ≤ 2 * C := by
    exact poissonMixture_range hE01 hz _ (2 * C) (by positivity) (hinnerRange B)
  have houterENN := poissonGraphMeanENN_ofReal hE01 huRoot F (2 * C) (by positivity)
    (fun B => hFRange B)
  have hlistENN (B : MGraph V) :
      ENNReal.ofReal (F B) = uniformPoissonListMeanENN z
        (fun xs => ENNReal.ofReal (g (addRoot B xs))) := by
    exact listPoissonMeanENN_ofReal hE01 hz (fun xs => g (addRoot B xs)) (2 * C)
      (by positivity) (fun xs => hgRange (addRoot B xs))
  have hrootENN := hroot (V := V) hV t (fun G => ENNReal.ofReal (g G)) ht
  have hshiftENN : ENNReal.ofReal (poissonGraphMean t g) =
      ENNReal.ofReal (poissonGraphMean uRoot F) := by
    calc
      ENNReal.ofReal (poissonGraphMean t g) =
          poissonGraphMeanENN t (fun G => ENNReal.ofReal (g G)) := hleftENN
      _ = poissonGraphMeanENN uRoot
          (fun B => uniformPoissonListMeanENN z
            (fun xs => ENNReal.ofReal (g (addRoot B xs)))) := hrootENN
      _ = poissonGraphMeanENN uRoot (fun B => ENNReal.ofReal (F B)) := by
        congr 1
        funext B
        exact (hlistENN B).symm
      _ = ENNReal.ofReal (poissonGraphMean uRoot F) := houterENN.symm
  have hleftRange := poissonGraphMean_range hE01 ht g (2 * C) (by positivity)
    (fun G => hgRange G)
  have hrightRange := poissonGraphMean_range hE01 huRoot F (2 * C) (by positivity)
    (fun B => hFRange B)
  have hshift : poissonGraphMean t g = poissonGraphMean uRoot F :=
    ofReal_eq_ofReal_of_nonneg hleftRange.1 hrightRange.1 hshiftENN
  have hleftAffine := poissonGraphMean_add_const hE01 ht f C hC hCbound C
  have hinnerAffine (B : MGraph V) :
      poissonMixture z (fun j => listMean j (fun xs => f (addRoot B xs) + C)) =
        poissonMixture z (fun j => listMean j (fun xs => f (addRoot B xs))) + C := by
    apply poissonListMean_add_const hE01 hz (fun xs => f (addRoot B xs)) C hC
    · intro xs
      exact hCbound (addRoot B xs)
  let F₀ : MGraph V → ℝ := fun B => poissonMixture z
    (fun j => listMean j (fun xs => f (addRoot B xs)))
  have hF₀bound (B : MGraph V) : |F₀ B| ≤ C := by
    exact poissonListMean_abs_le hE01 hz (fun xs => f (addRoot B xs)) C hC
      (fun xs => hCbound (addRoot B xs))
  have houterAffine := poissonGraphMean_add_const hE01 huLeaf F₀ C hC hF₀bound C
  have hshiftLeaf : poissonGraphMean t g = poissonGraphMean uLeaf F := by
    simpa only [huEq] using hshift
  have hfinal := hshiftLeaf
  rw [show g = (fun G => f G + C) from rfl, hleftAffine] at hfinal
  have hFaffine : F = fun B => F₀ B + C := by
    funext B
    exact hinnerAffine B
  rw [hFaffine, houterAffine] at hfinal
  linarith

end ThLean.W.S550
