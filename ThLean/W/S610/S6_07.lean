import ThLean.BP.S6.Foundation

noncomputable section
open scoped BigOperators
open ThresholdFoundations ThLean.BP.S6
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S610

private def sym2Perm {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Sym2 (Fin n) ≃ Sym2 (Fin n) where
  toFun := Sym2.map π
  invFun := Sym2.map π.symm
  left_inv := by
    intro e
    simp [Sym2.map_map, Function.comp_def]
  right_inv := by
    intro e
    simp [Sym2.map_map, Function.comp_def]

private def pairPerm {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Edge n ≃ Edge n where
  toFun e := ⟨Sym2.map π e.val, by
    intro v hv
    have heq : Sym2.map π e.val = Sym2.map π (s(π.symm v, π.symm v)) := by
      simpa using hv
    exact e.property (π.symm v) ((Sym2.map.injective π.injective) heq)
  ⟩
  invFun e := ⟨Sym2.map π.symm e.val, by
    intro v hv
    have heq : Sym2.map π.symm e.val =
        Sym2.map π.symm (s(π v, π v)) := by simpa using hv
    exact e.property (π v) ((Sym2.map.injective π.symm.injective) heq)
  ⟩
  left_inv := by
    intro e
    apply Subtype.ext
    simp [Sym2.map_map, Function.comp_def]
  right_inv := by
    intro e
    apply Subtype.ext
    simp [Sym2.map_map, Function.comp_def]

private theorem relabel_apply {n : ℕ} (π : Equiv.Perm (Fin n))
    (G : Graph n) (e : Sym2 (Fin n)) :
    relabel π G e = G ((sym2Perm π).symm e) := by
  classical
  unfold ThresholdFoundations.relabel ThresholdFoundations.mapGraph
  rw [Fintype.sum_eq_single ((sym2Perm π).symm e)]
  · simp [sym2Perm, Sym2.map_map, Function.comp_def]
  · intro x hne
    have hneq : Sym2.map π x ≠ e := by
      intro hx'
      apply hne
      apply (Sym2.map.injective π.injective)
      calc
        Sym2.map π x = e := hx'
        _ = Sym2.map π ((sym2Perm π).symm e) := by
          simp [sym2Perm, Sym2.map_map, Function.comp_def]
    simp [hneq]

private theorem relabel_on_image {n : ℕ} (π : Equiv.Perm (Fin n))
    (G : Graph n) (e : Sym2 (Fin n)) :
    relabel π G (Sym2.map π e) = G e := by
  rw [relabel_apply]
  simp [sym2Perm, Sym2.map_map, Function.comp_def]

private theorem touches_relabel {n : ℕ} (π : Equiv.Perm (Fin n))
    (a : Fin n) (e : Sym2 (Fin n)) :
    Touches (π a) (Sym2.map π e) ↔ Touches a e := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨π.symm v, ?_⟩
    have hh : Sym2.map π e = Sym2.map π (s(a, π.symm v)) := by
      simpa using hv
    exact (Sym2.map.injective π.injective) hh
  · rintro ⟨v, hv⟩
    refine ⟨π v, ?_⟩
    simpa using congrArg (Sym2.map π) hv

private theorem relabel_isColoring {n q : ℕ} (π : Equiv.Perm (Fin n))
    (G : Graph n) (σ : Fin n → Fin q) :
    IsColoring q (relabel π G) σ ↔ IsColoring q G (σ ∘ π) := by
  constructor
  · intro h a b hab
    have h' := h (π a) (π b)
    rw [← Sym2.map_mk π a b, relabel_on_image] at h'
    exact h' (by simpa using hab)
  · intro h a b hab
    have h' := h (π.symm a) (π.symm b)
    have hrel : relabel π G (s(a, b)) = G (s(π.symm a, π.symm b)) := by
      rw [relabel_apply]
      simp [sym2Perm, Sym2.map_map, Function.comp_def]
    rw [hrel] at hab
    have h'' := h' hab
    simpa [Function.comp_def] using h''

private theorem colorable_relabel {n q : ℕ} (π : Equiv.Perm (Fin n))
    (G : Graph n) : Colorable q (relabel π G) ↔ Colorable q G := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ ∘ π, (relabel_isColoring π G σ).mp hσ⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨σ ∘ π.symm, ?_⟩
    apply (relabel_isColoring π G (σ ∘ π.symm)).mpr
    simpa [Function.comp_def] using hσ

private theorem frozen_relabel {n q : ℕ} (π : Equiv.Perm (Fin n))
    (G : Graph n) (a b : Fin n) :
    Frozen q (relabel π G) (π a) (π b) ↔ Frozen q G a b := by
  constructor
  · rintro ⟨hc, hf⟩
    refine ⟨(colorable_relabel π G).mp hc, ?_⟩
    intro σ hσ
    have hrel : IsColoring q (relabel π G) (σ ∘ π.symm) := by
      apply (relabel_isColoring π G (σ ∘ π.symm)).mpr
      simpa [Function.comp_def] using hσ
    have heq := hf (σ ∘ π.symm) hrel
    simpa [Function.comp_def] using heq
  · rintro ⟨hc, hf⟩
    refine ⟨(colorable_relabel π G).mpr hc, ?_⟩
    intro σ hσ
    have horig : IsColoring q G (σ ∘ π) := (relabel_isColoring π G σ).mp hσ
    have heq := hf (σ ∘ π) horig
    simpa [Function.comp_def] using heq

private theorem degree_relabel {n : ℕ} (π : Equiv.Perm (Fin n))
    (G : Graph n) (a : Fin n) : degree (relabel π G) (π a) = degree G a := by
  unfold degree
  calc
    (∑ e : Sym2 (Fin n), if Touches (π a) e then relabel π G e else 0)
        = ∑ e : Sym2 (Fin n),
            if Touches (π a) (Sym2.map π e) then relabel π G (Sym2.map π e) else 0 := by
          symm
          exact Equiv.sum_comp (sym2Perm π)
            (fun e => if Touches (π a) e then relabel π G e else 0)
    _ = ∑ e : Sym2 (Fin n), if Touches a e then G e else 0 := by
          apply Finset.sum_congr rfl
          intro e he
          rw [relabel_on_image]
          simp only [touches_relabel]

private theorem frozenClass_relabel {n q : ℕ} (π : Equiv.Perm (Fin n))
    (G : Graph n) (u : Fin n) :
    frozenClass q (relabel π G) (π u) = (frozenClass q G u).image π := by
  ext a
  simp only [Finset.mem_image, frozenClass, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · intro ha
    refine ⟨π.symm a, ?_, ?_⟩
    · have ha' : Frozen q (relabel π G) (π u) (π (π.symm a)) := by simpa using ha
      exact (frozen_relabel π G u (π.symm a)).1 ha'
    · simp
  · rintro ⟨b, hb, rfl⟩
    exact (frozen_relabel π G u b).2 hb

private theorem relation_relabel_mem {n q : ℕ} (π : Equiv.Perm (Fin n))
    (G : Graph n) (u a b : Fin n) :
    (π a, π b) ∈ relation q (relabel π G) (π u) ↔
      (a, b) ∈ relation q G u := by
  simp only [relation, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hc, hfa, hfb, hcol⟩
    refine ⟨(colorable_relabel π G).mp hc, ?_, ?_, ?_⟩
    · intro hf
      exact hfa ((frozen_relabel π G u a).2 hf)
    · intro hf
      exact hfb ((frozen_relabel π G u b).2 hf)
    · intro σ hσ
      have hrel : IsColoring q (relabel π G) (σ ∘ π.symm) := by
        apply (relabel_isColoring π G (σ ∘ π.symm)).mpr
        simpa [Function.comp_def] using hσ
      have heq := hcol (σ ∘ π.symm) hrel
      simpa [Function.comp_def] using heq
  · rintro ⟨hc, hfa, hfb, hcol⟩
    refine ⟨(colorable_relabel π G).mpr hc, ?_, ?_, ?_⟩
    · intro hf
      exact hfa ((frozen_relabel π G u a).1 hf)
    · intro hf
      exact hfb ((frozen_relabel π G u b).1 hf)
    · intro σ hσ
      have horig : IsColoring q G (σ ∘ π) := (relabel_isColoring π G σ).mp hσ
      have heq := hcol (σ ∘ π) horig
      simpa [Function.comp_def] using heq

private theorem relation_relabel {n q : ℕ} (π : Equiv.Perm (Fin n))
    (G : Graph n) (u : Fin n) :
    relation q (relabel π G) (π u) =
      (relation q G u).image (fun ab => (π ab.1, π ab.2)) := by
  ext ab
  constructor
  · intro hab
    refine Finset.mem_image.mpr ⟨(π.symm ab.1, π.symm ab.2), ?_, ?_⟩
    · have hpair : (π (π.symm ab.1), π (π.symm ab.2)) = ab := by
        ext <;> simp
      have hab' : (π (π.symm ab.1), π (π.symm ab.2)) ∈
          relation q (relabel π G) (π u) := hpair.symm ▸ hab
      exact (relation_relabel_mem π G u (π.symm ab.1) (π.symm ab.2)).mp hab'
    · simp
  · intro hab
    rcases Finset.mem_image.mp hab with ⟨cd, hcd, hcdab⟩
    have hrel := (relation_relabel_mem π G u cd.1 cd.2).mpr hcd
    exact hcdab ▸ hrel

private theorem beta_relabel {n q : ℕ} (π : Equiv.Perm (Fin n))
    (G : Graph n) (u : Fin n) : beta q (relabel π G) (π u) = beta q G u := by
  unfold beta
  rw [relation_relabel]
  congr 1
  exact_mod_cast (Finset.card_image_of_injective (relation q G u)
    (f := fun ab : Fin n × Fin n => (π ab.1, π ab.2)) (by
      intro x y hxy
      exact Prod.ext (π.injective (congrArg Prod.fst hxy))
        (π.injective (congrArg Prod.snd hxy))))

private theorem erase_relabel_apply {n : ℕ} (π : Equiv.Perm (Fin n))
    (G : Graph n) (e : Sym2 (Fin n)) (f : Sym2 (Fin n)) :
    eraseEdge (relabel π G) (Sym2.map π e) (Sym2.map π f) =
      eraseEdge G e f := by
  by_cases h : f = e
  · subst f
    simp [eraseEdge, relabel_on_image]
  · have hmap : Sym2.map π f ≠ Sym2.map π e := by
      intro hm
      exact h ((Sym2.map.injective π.injective) hm)
    simp [eraseEdge, h, hmap, relabel_on_image]

private theorem erase_relabel {n : ℕ} (π : Equiv.Perm (Fin n))
    (G : Graph n) (e : Sym2 (Fin n)) :
    eraseEdge (relabel π G) (Sym2.map π e) = relabel π (eraseEdge G e) := by
  funext f
  by_cases h : f = Sym2.map π e
  · subst f
    simp [eraseEdge, relabel_on_image]
  · have h' : (sym2Perm π).symm f ≠ e := by
      intro he
      apply h
      calc
        f = Sym2.map π ((sym2Perm π).symm f) := by
          simp [sym2Perm, Sym2.map_map, Function.comp_def]
        _ = Sym2.map π e := congrArg (Sym2.map π) he
    rw [relabel_apply]
    simp [eraseEdge, h, h', relabel_apply]

private theorem nonpivotalCount_relabel {n q : ℕ} (π : Equiv.Perm (Fin n))
    (G : Graph n) (u v : Fin n) :
    nonpivotalCount q (relabel π G) (π u) (π v) = nonpivotalCount q G u v := by
  classical
  unfold nonpivotalCount
  calc
    (∑ e : Sym2 (Fin n),
      if Touches (π u) e ∧ Frozen q (relabel π G) (π u) (π v) ∧
        Frozen q (eraseEdge (relabel π G) e) (π u) (π v)
      then relabel π G e else 0)
      = ∑ e : Sym2 (Fin n),
        if Touches (π u) (Sym2.map π e) ∧ Frozen q (relabel π G) (π u) (π v) ∧
          Frozen q (eraseEdge (relabel π G) (Sym2.map π e)) (π u) (π v)
        then relabel π G (Sym2.map π e) else 0 := by
          convert (Equiv.sum_comp (sym2Perm π)
            (fun e => if Touches (π u) e ∧ Frozen q (relabel π G) (π u) (π v) ∧
              Frozen q (eraseEdge (relabel π G) e) (π u) (π v)
              then relabel π G e else 0)).symm using 1
          all_goals simp only [sym2Perm]
          all_goals rfl
    _ = ∑ e : Sym2 (Fin n),
        if Touches u e ∧ Frozen q G u v ∧ Frozen q (eraseEdge G e) u v
        then G e else 0 := by
          apply Finset.sum_congr rfl
          intro e he
          rw [relabel_on_image]
          rw [frozen_relabel π G u v]
          rw [erase_relabel π G e]
          rw [frozen_relabel π (eraseEdge G e) u v]
          simp only [touches_relabel]

private theorem doubleSum_relabel {n : ℕ} (π : Equiv.Perm (Fin n))
    (P Q : Fin n → Fin n → Prop)
    (h : ∀ a b, P (π a) (π b) ↔ Q a b) :
    (∑ a : Fin n, ∑ b : Fin n, indicator (P a b)) =
      ∑ a : Fin n, ∑ b : Fin n, indicator (Q a b) := by
  calc
    (∑ a : Fin n, ∑ b : Fin n, indicator (P a b))
        = ∑ a : Fin n, ∑ b : Fin n, indicator (P a (π b)) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact (Equiv.sum_comp π (fun b => indicator (P a b))).symm
    _ = ∑ a : Fin n, ∑ b : Fin n, indicator (P (π a) (π b)) := by
          exact (Equiv.sum_comp π (fun a => ∑ b : Fin n, indicator (P a (π b)))).symm
    _ = ∑ a : Fin n, ∑ b : Fin n, indicator (Q a b) := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          simp [h]

private theorem kappaDegree_relabel {n q j : ℕ} (π : Equiv.Perm (Fin n))
    (G : Graph n) : kappaDegree q j (relabel π G) = kappaDegree q j G := by
  unfold kappaDegree
  congr 1
  apply doubleSum_relabel π _ _
  intro a b
  simp [degree_relabel, frozen_relabel]

private theorem kappaDegreeNP_relabel {n q K j : ℕ} (π : Equiv.Perm (Fin n))
    (G : Graph n) :
    kappaDegreeNP q K j (relabel π G) = kappaDegreeNP q K j G := by
  unfold kappaDegreeNP
  congr 1
  apply doubleSum_relabel π _ _
  intro a b
  simp [degree_relabel, frozen_relabel, nonpivotalCount_relabel]

private theorem kappaDegreePiv_relabel {n q K j : ℕ} (π : Equiv.Perm (Fin n))
    (G : Graph n) :
    kappaDegreePiv q K j (relabel π G) = kappaDegreePiv q K j G := by
  unfold kappaDegreePiv
  congr 1
  apply doubleSum_relabel π _ _
  intro a b
  simp [degree_relabel, frozen_relabel, nonpivotalCount_relabel]

private def historyPerm {n m : ℕ} (π : Equiv.Perm (Fin n)) : Hist n m ≃ Hist n m :=
  Equiv.arrowCongr (Equiv.refl (Fin m)) (pairPerm π)

private theorem tupleGraph_relabel {n m : ℕ} (π : Equiv.Perm (Fin n))
    (x : Hist n m) : tupleGraph (historyPerm π x) = relabel π (tupleGraph x) := by
  funext e
  rw [relabel_apply]
  unfold tupleGraph
  apply congrArg Finset.card
  apply Finset.ext
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [historyPerm, pairPerm]
  change (sym2Perm π) (x i).val = e ↔ (x i).val = (sym2Perm π).symm e
  exact Equiv.apply_eq_iff_eq_symm_apply (sym2Perm π)

private theorem uniformMean_historyPerm {n m : ℕ} (π : Equiv.Perm (Fin n))
    (F : Hist n m → ℝ) : uniformMean (fun x => F (historyPerm π x)) = uniformMean F := by
  unfold uniformMean
  rw [Equiv.sum_comp (historyPerm π) F]

private theorem meanGraph_relabel {n m : ℕ} (π : Equiv.Perm (Fin n))
    (F : Graph n → ℝ) :
    meanGraph m (fun H => F (relabel π H)) = meanGraph m F := by
  unfold meanGraph
  have h := uniformMean_historyPerm π (fun x : Hist n m => F (tupleGraph x))
  calc
    uniformMean (fun x : Hist n m => F (relabel π (tupleGraph x)))
        = uniformMean (fun x => F (tupleGraph (historyPerm π x))) := by
          unfold uniformMean
          congr 1
          apply Finset.sum_congr rfl
          intro x hx
          exact (congrArg F (tupleGraph_relabel π x)).symm
    _ = uniformMean (fun x : Hist n m => F (tupleGraph x)) := h

theorem S6_07Statement_holds : ThLean.BP.S6.S6_07Statement := by
  intro n q hn hq π G u j K hK
  refine ⟨colorable_relabel π G, degree_relabel π G u, ?_, ?_, beta_relabel π G u,
    kappaDegree_relabel π G, kappaDegreeNP_relabel π G, kappaDegreePiv_relabel π G,
    ?_, ?_⟩
  · exact frozenClass_relabel π G u
  · exact relation_relabel π G u
  · intro m F
    exact meanGraph_relabel π F
  · intro m
    exact ⟨historyPerm π, tupleGraph_relabel π, uniformMean_historyPerm π⟩

end ThLean.W.S610
