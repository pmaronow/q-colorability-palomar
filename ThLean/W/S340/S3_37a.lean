import ThLean.BP.S3.Poisson
import ThLean.Contrib.S340.S3_37aCore

universe u

namespace ThLean.W.S340

/-- Conditional assembly. The outstanding core node is recorded in
`ThLean.Contrib.S340.S3_37aCoreStatement`. -/
theorem S3_37aStatement_holds
    (h : ThLean.Contrib.S340.S3_37aCoreStatement.{u}) :
    ThLean.BP.S3.S3_37aStatement.{u} := h

end ThLean.W.S340
