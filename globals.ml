let dedukti_out =
  let oc = open_out "dedukti_out.dk" in
  Format.formatter_of_out_channel oc
    
let max_pred = ref 0
