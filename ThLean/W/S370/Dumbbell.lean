import ThLean.Contrib.S370.Dumbbell

universe u

namespace ThLean.W.S370

/-- Assembly of the two transparent proof obligations introduced for S3-67. -/
theorem S3_67Statement_of_helpers
    (hdecode : ThLean.Contrib.S370.S3_67DecodeStatement.{u})
    (hcode : ThLean.Contrib.S370.S3_67CodeStatement.{u}) :
    ThLean.BP.S3.S3_67Statement.{u} := by
  intro V inst
  exact ⟨hdecode V, hcode V⟩

end ThLean.W.S370
