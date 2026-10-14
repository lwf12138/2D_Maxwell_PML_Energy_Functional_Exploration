import LeanPML.PML.WeakCoefficients
import LeanPML.Examples.WeakSpaces

/-!
# 区域弱系数乘积法则的非零调用

复用 v0.5 的真实二维物理区 bump；不是新的 PDE 解或弱主定理。
调用 WeakCoefficients 的一般 H₀¹→H¹ 构造，验证输入空间及输出函数非零。
-/
noncomputable section
open LeanPML.Rectangle LeanPML.Rectangle.ParameterCertificate
namespace LeanPML.PML

/-- 非零 H₀¹ 输入来自已有紧支光滑成员证明，没有重新假设所需成员资格。 -/
def weakCoefficientExampleInput : zeroBoundaryGraph unitSquare :=
  ⟨smoothToWeakH1 unitSquare LeanPML.Examples.WeakSpaces.physicalTest.field,
    LeanPML.Examples.WeakSpaces.physicalTest_nonzero_member.1⟩

/-- 在实际二维矩形上调用一般弱乘积构造，结果函数仍非零。
常数 1 只用于简洁核验调用链；一般乘积定理接受真正分布意义的 W¹,∞ 系数。 -/
theorem weakCoefficient_nonzero_call :
    (weakCoefficientMul unitSquare
      (weakCoefficientOfSmooth unitSquare weakCoefficientOne)
      weakCoefficientExampleInput).val 0 ≠ 0 := by
  rw [weakCoefficient_one_value]
  exact LeanPML.Examples.WeakSpaces.physicalTest_nonzero_member.2

end LeanPML.PML
