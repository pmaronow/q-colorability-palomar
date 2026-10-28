import ThLean.W.S369S.DecodeLists
import ThLean.W.S369S.CodeLists

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
namespace ThLean.W.S369S
open ThresholdFoundations ThLean.BP.S3

theorem exactTheta_decode {V : Type u} [Fintype V] (G : MGraph V) (hG : ExactTheta G) :
    let k := (vertexSupport G).card
    2 ≤ k ∧ edgeCount G = k+1 ∧
    ∃ (hk : 0 < k) (j₁ j₂ j₃ : ℕ) (v : Fin k ↪ V),
      1 ≤ j₁ ∧ 1 ≤ j₂ ∧ 1 ≤ j₃ ∧ j₁+j₂+j₃ = k+1 ∧
      G = thetaCode hk j₁ j₂ j₃ v := by
  obtain ⟨a, b, x, y, z, hn, rfl⟩ := exactTheta_lists hG
  let L := thetaLabels a b x y z
  have hcard : (vertexSupport (thetaLists a b x y z)).card = L.length := by
    rw [support_thetaLists, List.toFinset_card_of_nodup hn]
  dsimp only
  rw [hcard]
  have hk2 : 2 ≤ L.length := by simp [L, thetaLabels]
  have hk : 0 < L.length := by omega
  have hs : (x.length+1)+(y.length+1)+(z.length+1) = L.length+1 := by
    simp [L, thetaLabels]; omega
  let v : Fin L.length ↪ V := ⟨L.get, fun _ _ h => hn.get_inj_iff.mp h⟩
  have heq : thetaLists a b x y z =
      thetaCode hk (x.length+1) (y.length+1) (z.length+1) v :=
    (thetaCode_get_labels a b x y z hk).symm
  refine ⟨hk2, ?_, hk, x.length+1, y.length+1, z.length+1, v,
    by omega, by omega, by omega, hs, heq⟩
  rw [heq]
  exact ThLean.W.S369.thetaCode_edgeCount hk _ _ _ v (by omega) (by omega) (by omega) hs

/-- The original theta encoding and size leaf, with no additional premises. -/
theorem S3_66Statement_holds : ThLean.BP.S3.S3_66Statement.{u} := by
  intro V inst
  constructor
  · exact exactTheta_decode
  · intro k hk j₁ j₂ j₃ v _ h₁ h₂ h₃ hs
    obtain ⟨hexact, hsupport⟩ := thetaCode_exact_support hk j₁ j₂ j₃ v h₁ h₂ h₃ hs
    exact ⟨hexact, hsupport, ThLean.W.S369.thetaCode_edgeCount hk j₁ j₂ j₃ v h₁ h₂ h₃ hs⟩

example : ThLean.BP.S3.S3_66Statement.{u} := S3_66Statement_holds

end ThLean.W.S369S
