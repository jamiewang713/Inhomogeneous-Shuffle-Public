import RiffleLowerV2.ProfileTransfer.Margin
#check RiffleLowerV2.ProfileTransfer.marginTransfer
#print axioms RiffleLowerV2.ProfileTransfer.marginTransfer
#print axioms RiffleLowerV2.ProfileTransfer.alphaDomain_nonempty
#print axioms RiffleLowerV2.ProfileTransfer.alphaInf_bounds
#print axioms RiffleLowerV2.ProfileTransfer.alphaInf_le_add
#print axioms RiffleLowerV2.ProfileTransfer.variational_le_of_lift
example : RiffleLowerV2.Targets.MarginTransferTarget :=
  RiffleLowerV2.ProfileTransfer.marginTransfer
