import ThLean.W.S368S.Components
import ThLean.W.S368S.Transport

noncomputable section
universe u
namespace ThLean.W.S368S
open ThresholdFoundations ThLean.BP.S3

/-- A noncolorable component contains an excess-one witness; its encoding
transports the witness along the inclusion into the original vertex set. -/
theorem S3_65Statement_of_deps
    (h55 : S3_55Statement.{u}) (h56 : S3_56Statement.{u})
    (h57a : S3_57aStatement.{u}) (h63a : S3_63aStatement.{u})
    (h63b : S3_63bStatement.{u}) (h66 : S3_66Statement.{u})
    (h67 : S3_67Statement.{u}) : S3_65Statement.{u} := by
  classical
  intro V _ q hq _ G hG hnot
  obtain ⟨C, hC, hbad⟩ := exists_bad_component q (by omega) G hG hnot
  let H := componentGraph G C
  have hH : Loopless H := componentGraph_loopless G hG C
  have hconn : (graphSupport H).Connected := componentGraph_connected G C
  have hlarge : Fintype.card C < edgeCount H := by
    by_contra h
    apply hbad
    exact S3_57_assembly h55 h56 h57a C q hq hC H hH hconn (by omega)
  obtain ⟨F, hFG, _, hshape⟩ := h63b C H hH
    (h63a C hC H hH hconn (by omega))
  have hlift : subgraph (mapGraph Subtype.val F) G :=
    mapGraph_subgraph Subtype.val Subtype.val_injective F G hFG
  let k := (vertexSupport F).card
  have hbound : k ≤ Fintype.card V :=
    (Finset.card_le_univ _).trans
      (Fintype.card_le_of_injective Subtype.val Subtype.val_injective)
  let embed : C ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  rcases hshape with htheta | hdumbbell
  · obtain ⟨hk2, _, hk, j₁, j₂, j₃, labels, hj₁, hj₂, hj₃, hsum, hcode⟩ :=
      (h66 C).1 F htheta
    let labels' := labels.trans embed
    have hmap : mapGraph Subtype.val F = thetaCode hk j₁ j₂ j₃ labels' := by
      exact (congrArg (mapGraph (Subtype.val : C → V)) hcode).trans
        (mapGraph_thetaCode hk j₁ j₂ j₃ Subtype.val labels)
    rw [hmap] at hlift
    obtain ⟨hexact, hcard, hedge⟩ :=
      (h66 V).2 k hk j₁ j₂ j₃ labels' hk2 hj₁ hj₂ hj₃ hsum
    exact ⟨k, thetaCode hk j₁ j₂ j₃ labels', hk2, hbound, hlift,
      ⟨loopless_of_subgraph _ G hlift hG, hcard, Or.inl hexact⟩, hedge⟩
  · obtain ⟨hk2, _, hk, j₁, j₂, j₃, labels, hj₁, hj₂, hsum, hcode⟩ :=
      (h67 C).1 F hdumbbell
    let labels' := labels.trans embed
    have hmap : mapGraph Subtype.val F = dumbbellCode hk j₁ j₂ j₃ labels' := by
      exact (congrArg (mapGraph (Subtype.val : C → V)) hcode).trans
        (mapGraph_dumbbellCode hk j₁ j₂ j₃ Subtype.val labels)
    rw [hmap] at hlift
    obtain ⟨hexact, hcard, hedge⟩ :=
      (h67 V).2 k hk j₁ j₂ j₃ labels' hk2 hj₁ hj₂ hsum
    exact ⟨k, dumbbellCode hk j₁ j₂ j₃ labels', hk2, hbound, hlift,
      ⟨loopless_of_subgraph _ G hlift hG, hcard, Or.inr hexact⟩, hedge⟩

example (h55 : S3_55Statement.{u}) (h56 : S3_56Statement.{u})
    (h57a : S3_57aStatement.{u}) (h63a : S3_63aStatement.{u})
    (h63b : S3_63bStatement.{u}) (h66 : S3_66Statement.{u})
    (h67 : S3_67Statement.{u}) : ThLean.BP.S3.S3_65Statement.{u} :=
  S3_65Statement_of_deps h55 h56 h57a h63a h63b h66 h67

end ThLean.W.S368S
