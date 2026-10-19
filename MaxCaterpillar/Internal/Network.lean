import MaxCaterpillar.Definitions
import MaxNN.Constructions.MaxN.Width.TwoLayer

/-! Exact bridges between the public formula and the internal network model.
No positivity assumption is imposed on either hidden width. -/

namespace MaxCaterpillar.Internal

open MaxNN

def ofLayers {N h₁ h₂ : ℕ}
    (T₁ : Affine N h₁) (T₂ : Affine h₁ h₂) (T₃ : Affine h₂ 1) :
    Network N h₁ h₂ :=
  ⟨T₁.A, T₁.b, T₂.A, T₂.b, T₃.A 0, T₃.b 0⟩

theorem ofLayers_eval {N h₁ h₂ : ℕ}
    (T₁ : Affine N h₁) (T₂ : Affine h₁ h₂) (T₃ : Affine h₂ 1) (x : Point N) :
    (ofLayers T₁ T₂ T₃).eval x =
      (ReLUNet.layer T₁ (ReLUNet.layer T₂ (ReLUNet.affine T₃))).eval x 0 := rfl

def toReLUNet {N h₁ h₂ : ℕ} (net : Network N h₁ h₂) : ReLUNet N 1 2 :=
  .layer ⟨net.W₁, net.b₁⟩
    (.layer ⟨net.W₂, net.b₂⟩ (.affine ⟨fun _ => net.w₃, fun _ => net.b₃⟩))

theorem toReLUNet_eval {N h₁ h₂ : ℕ} (net : Network N h₁ h₂) (x : Point N) :
    (toReLUNet net).eval x 0 = net.eval x := rfl

/-- Exact equivalence, preserving both widths and the function on all inputs. -/
theorem twoLayerWidth_iff {N h₁ h₂ : ℕ} {f : Point N → ℝ} :
    Width.TwoLayerWidth N h₁ h₂ f ↔
      ∃ net : Network N h₁ h₂, ∀ x, net.eval x = f x :=
  ⟨fun ⟨T₁, T₂, .affine T₃, h⟩ => ⟨ofLayers T₁ T₂ T₃, h⟩, fun ⟨net, h⟩ =>
    ⟨⟨net.W₁, net.b₁⟩, ⟨net.W₂, net.b₂⟩, .affine ⟨fun _ => net.w₃, fun _ => net.b₃⟩, h⟩⟩

end MaxCaterpillar.Internal
