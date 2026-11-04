module

public import ThLean.BP.S3.Cycles

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S366
open ThresholdFoundations

universe u
variable {V : Type u} [Fintype V]

private theorem card_occurrence (G : MGraph V) : Fintype.card (Occurrence G) = edgeCount G := by
  simp [Occurrence, edgeCount, Fintype.card_sigma]

private theorem occLift_injective {T K : MGraph V} (h : subgraph T K) :
    Function.Injective (ThLean.BP.S3.OccLift h) := by
  intro x y hxy
  rcases x with ⟨e, i⟩
  rcases y with ⟨f, j⟩
  have hef : e = f := congrArg Sigma.fst hxy
  have hval : i.val = j.val := by
    simpa [ThLean.BP.S3.OccLift] using
      congrArg (fun z : Occurrence K => z.2.val) hxy
  subst f
  congr 1
  exact Fin.ext hval

private theorem cycle_occ_touches_vertices (G : MGraph V) (c : OccurrenceCycle G)
    (o : Occurrence G) (ho : o ∈ cycleOccurrences c) :
    ∀ x, x ∈ o.1 → x ∈ cycleVertices c := by
  rcases Finset.mem_image.mp ho with ⟨i, -, hio⟩
  intro x hx
  have hlen : 2 ≤ c.length := c.length_ge_two
  have hed : o.1 = Sym2.mk (c.vertex i) (c.vertex ⟨(i.val + 1) % c.length,
      Nat.mod_lt _ (by omega)⟩) := by
    calc
      o.1 = (c.edge i).1 := (congrArg Sigma.fst hio).symm
      _ = Sym2.mk (c.vertex i) (c.vertex ⟨(i.val + 1) % c.length, Nat.mod_lt _ (by omega)⟩) :=
        c.joins i
  rw [hed, Sym2.mem_iff] at hx
  rcases hx with hx | hx
  · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hx.symm⟩
  · exact Finset.mem_image.mpr ⟨⟨(i.val + 1) % c.length,
      Nat.mod_lt _ (by omega)⟩, Finset.mem_univ _, hx.symm⟩

private theorem cycle_occ_disjoint_of_small_vertex_inter (K : MGraph V)
    (hK : Loopless K) (c d : OccurrenceCycle K)
    (hv : (cycleVertices c ∩ cycleVertices d).card ≤ 1) :
    Disjoint (cycleOccurrences c) (cycleOccurrences d) := by
  apply Finset.disjoint_left.mpr
  intro o hoc hod
  have hpos : 0 < K o.1 := by
    have hlt := o.2.isLt
    omega
  let a := o.1.out.1
  let b := o.1.out.2
  have hpair : o.1 = Sym2.mk a b := o.1.out_eq.symm
  have hab : a ≠ b := by
    intro hab
    have hdiag : o.1 = Sym2.mk a a := by
      calc
        o.1 = Sym2.mk a b := hpair
        _ = Sym2.mk a a := by rw [hab]
    rw [hdiag, hK a] at hpos
    omega
  have ha : a ∈ o.1 := Sym2.out_fst_mem _
  have hb : b ∈ o.1 := Sym2.out_snd_mem _
  have hac : a ∈ cycleVertices c := cycle_occ_touches_vertices K c o hoc a ha
  have hbc : b ∈ cycleVertices c := cycle_occ_touches_vertices K c o hoc b hb
  have had : a ∈ cycleVertices d := cycle_occ_touches_vertices K d o hod a ha
  have hbd : b ∈ cycleVertices d := cycle_occ_touches_vertices K d o hod b hb
  have hpairs : ({a, b} : Finset V) ⊆ cycleVertices c ∩ cycleVertices d := by
    intro x hx
    rw [Finset.mem_inter]
    rcases Finset.mem_insert.mp hx with hxa | hxb
    · subst x
      exact ⟨hac, had⟩
    · have hxb' : x = b := Finset.mem_singleton.mp hxb
      subst x
      exact ⟨hbc, hbd⟩
  have hcard : 2 ≤ (cycleVertices c ∩ cycleVertices d).card := by
    calc
      2 = ({a, b} : Finset V).card := by simp [hab]
      _ ≤ (cycleVertices c ∩ cycleVertices d).card := Finset.card_le_card hpairs
  omega

theorem S3_63aStatement_of_deps
    (h55 : ThLean.BP.S3.S3_55Statement.{u})
    (h58 : ThLean.BP.S3.S3_58Statement.{u})
    (h60 : ThLean.BP.S3.S3_60Statement.{u})
    (h61 : ThLean.BP.S3.S3_61Statement.{u})
    (h62 : ThLean.BP.S3.S3_62Statement.{u}) :
    ThLean.BP.S3.S3_63aStatement.{u} := by
  intro V _ hV K hK hconn hsize
  obtain ⟨T, hT, hcard, _, _⟩ := h55 V hV K hK hconn
  let hsub : subgraph T K := hT.2.1
  let lifted : Finset (Occurrence K) := Finset.univ.image (ThLean.BP.S3.OccLift hsub)
  let extras : Finset (Occurrence K) := Finset.univ \ lifted
  have hLiftSub : lifted ⊆ Finset.univ := Finset.subset_univ _
  have hLiftCard : lifted.card = edgeCount T := by
    dsimp [lifted]
    rw [Finset.card_image_of_injective _ (occLift_injective hsub)]
    exact card_occurrence T
  have hExtraCard : extras.card = edgeCount K - edgeCount T := by
    dsimp [extras]
    rw [Finset.card_sdiff_of_subset hLiftSub, Finset.card_univ, card_occurrence K,
      hLiftCard]
  have hExtraAtLeastTwo : 2 ≤ extras.card := by
    rw [hExtraCard]
    have hTK : edgeCount T + 2 ≤ edgeCount K := by omega
    omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < extras.card)
  have hp' : p ∈ extras := hp
  have hrest : 0 < (extras.erase p).card := by
    rw [Finset.card_erase_of_mem hp]
    omega
  obtain ⟨p', hp'⟩ := Finset.card_pos.mp hrest
  have hp'parts := Finset.mem_erase.mp hp'
  have hpp' : p ≠ p' := Ne.symm hp'parts.1
  have hpout : p ∉ lifted := (Finset.mem_sdiff.mp hp).2
  have hpout' : p' ∉ lifted := (Finset.mem_sdiff.mp hp'parts.2).2
  obtain ⟨c, d, hc, hd, hpnotc⟩ := h58 V K T hK hT hsub p p' hpp' hpout hpout'
  by_cases hvertices : 2 ≤ (cycleVertices c ∩ cycleVertices d).card
  · have hpinD : p' ∈ cycleOccurrences d := by
      have hmem : p' ∈ cycleOccurrences d \ lifted := by rw [hd]; simp
      exact (Finset.mem_sdiff.mp hmem).1
    obtain ⟨r, a, b, hrlen, hab, hrfrom, ha, hb, hrverts, hrocc, hpinr, hdisj⟩ :=
      h60 V K c d p' hpinD hpnotc hvertices
    exact Or.inl (h62 V K c r a b hrlen hab hrfrom ha hb hrverts hdisj)
  · have hsmall : (cycleVertices c ∩ cycleVertices d).card ≤ 1 := by omega
    have hdisj : Disjoint (cycleOccurrences c) (cycleOccurrences d) :=
      cycle_occ_disjoint_of_small_vertex_inter K hK c d hsmall
    exact Or.inr (h61 V K hK hconn c d hdisj hsmall).1

end ThLean.W.S366
