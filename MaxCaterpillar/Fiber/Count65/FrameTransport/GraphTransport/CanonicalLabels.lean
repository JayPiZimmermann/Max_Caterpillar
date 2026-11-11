import MaxCaterpillar.Fiber.Count65.SmallRootFrames

/-! # Ordered representatives of the independently checked finite frames

Only finite input labels occur here. The image equalities below connect the
ordered real-row patterns to the finite graph cover without assuming an order
for any actual network's rows.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.FrameTransport
open RootFrames SmallRootFrames

def twoCanonicalLabels (k : Fin 5) : Fin 2 → Root :=
  if k.val=0 then ![(0,1),(2,3)]
  else if k.val=1 then ![(0,1),(1,0)]
  else if k.val=2 then ![(0,1),(1,2)]
  else if k.val=3 then ![(0,1),(2,1)]
  else ![(1,0),(1,2)]

def threeCanonicalLabels (k : Fin 21) : Fin 3 → Root :=
  if k.val=0 then ![(0,1),(1,2),(0,2)]
  else if k.val=1 then ![(0,1),(1,2),(2,0)]
  else if k.val=2 then ![(0,1),(1,0),(1,2)]
  else if k.val=3 then ![(0,1),(1,0),(2,1)]
  else if k.val=4 then ![(0,1),(1,0),(2,3)]
  else if k.val<13 then
    ![orient (k.val-5) 0 0 1,orient (k.val-5) 1 1 2,orient (k.val-5) 2 2 3]
  else ![orient (k.val-13) 0 0 1,orient (k.val-13) 1 0 2,orient (k.val-13) 2 0 3]

theorem twoCanonical_eq_image (k : Fin 5) :
    twoCanonical k = Finset.univ.image (twoCanonicalLabels k) := by
  fin_cases k <;> decide

theorem threeCanonical_eq_image (k : Fin 21) :
    threeCanonical k = Finset.univ.image (threeCanonicalLabels k) := by
  fin_cases k <;> decide

#print axioms twoCanonical_eq_image
#print axioms threeCanonical_eq_image
end MaxCaterpillar.Fiber.Count65.FrameTransport
