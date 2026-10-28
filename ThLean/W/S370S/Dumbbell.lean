import ThLean.W.S370S.Shared
import ThLean.W.S370S.Joined
import ThLean.W.S370S.DecodeShared
import ThLean.W.S370S.DecodeJoined

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
namespace ThLean.W.S370S
open ThresholdFoundations ThLean.BP.S3
variable {V : Type u} [Fintype V]

theorem exactDumbbell_decode (G : MGraph V) (hG : ExactDumbbell G) :
    let k := (vertexSupport G).card
    2 ≤ k ∧ edgeCount G = k+1 ∧
    ∃ (hk : 0 < k) (j₁ j₂ j₃ : ℕ) (v : Fin k ↪ V),
      2 ≤ j₁ ∧ 2 ≤ j₂ ∧ j₁+j₂+j₃=k+1 ∧ G = dumbbellCode hk j₁ j₂ j₃ v := by
  refine ⟨(exactDumbbell_size hG).1,(exactDumbbell_size hG).2,?_⟩
  have hwhole := hG
  obtain ⟨c,d,hdis,hcase⟩ := hG
  rcases hcase with ⟨hcard,hcover⟩ | ⟨hv,p,a,b,hp,hfrom,ha,hb,hpa,hpb,hpd,hcover⟩
  · obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hcard
    have hac : a ∈ cycleVertices c :=
      (Finset.mem_inter.mp (by rw [ha]; simp)).1
    have had : a ∈ cycleVertices d :=
      (Finset.mem_inter.mp (by rw [ha]; simp)).2
    obtain ⟨c',_,hcv,hce,hc0⟩ := rotate_at c a hac
    obtain ⟨d',_,hdv,hde,hd0⟩ := rotate_at d a had
    obtain ⟨hk,v,hs,heq⟩ := decode_shared_oriented c' d' a hc0 hd0
      (by simpa only [hce,hde] using hdis)
      (by simpa only [hcv,hdv] using ha)
      (by simpa only [hce,hde] using hcover)
    exact ⟨hk,c'.length,d'.length,0,v,c'.length_ge_two,d'.length_ge_two,hs,heq⟩
  · obtain ⟨c',_,hcv,hce,hc0⟩ := rotate_at c a ha
    obtain ⟨d',_,hdv,hde,hd0⟩ := rotate_at d b hb
    obtain ⟨hk,v,hs,heq⟩ := decode_joined_oriented hwhole c' d' p a b hc0 hd0
      (by simpa only [hce,hde] using hdis)
      (by simpa only [hcv,hdv] using hv) hp hfrom
      (by simpa only [hcv] using hpa) (by simpa only [hdv] using hpb)
      (by simpa only [hce,hde] using hpd)
      (by simpa only [hce,hde] using hcover)
    exact ⟨hk,c'.length,d'.length,p.length,v,c'.length_ge_two,d'.length_ge_two,hs,heq⟩

/-- Dumbbell encoding, exact support size, and occurrence count at the original blueprint type. -/
theorem S3_67Statement_holds : ThLean.BP.S3.S3_67Statement.{u} := by
  intro V inst
  constructor
  · exact exactDumbbell_decode
  · intro k hk j₁ j₂ j₃ v _ h₁ h₂ hs
    have hc : ExactDumbbell (dumbbellCode hk j₁ j₂ j₃ v) ∧
        (vertexSupport (dumbbellCode hk j₁ j₂ j₃ v)).card = k := by
      by_cases h₃ : j₃=0
      · subst j₃
        exact dumbbellCode_shared hk j₁ j₂ v h₁ h₂ (by omega)
      · exact dumbbellCode_joined hk j₁ j₂ j₃ v h₁ h₂ (by omega) hs
    exact ⟨hc.1,hc.2,dumbbellCode_edgeCount hk j₁ j₂ j₃ v h₁ h₂ hs⟩

example : ThLean.BP.S3.S3_67Statement.{u} := S3_67Statement_holds

end ThLean.W.S370S
