let [@entry] main env (param : unit) (storage : unit) = /@\label{boomerang_main}@/
  let amount = Global.get_amount env in /@\label{boomerang_getamount}@/
  let ops =
    if Tz.eq amount (Tz 0) then [] /@\label{boomerang_tzeq}@/
    else
      let source_contract = Option.get (Contract.contract RepUnit (Global.get_source env)) in /@\label{boomerang_getsource}@/ /@\label{boomerang_contract}@/
      [ Operation.transfer_tokens ParamUnit amount source_contract ] /@\label{boomerang_transfertokens}@/
    in
    ops, ()
(*@ ops, stg = main env param storage /@\label{boomerang_gospel_start}@/
      ensures /@\label{boomerang_gospel_ensures_start}@/
        let amount = Global.get_amount env in
        if Tz.eq amount (Tz 0) then ops = [] /@\label{boomerang_gospel_ensures_if}@/
        else
          match Contract.contract RepUnit (Global.get_source env) with /@\label{boomerang_gospel_ensures_match_contract}@/
          | Some sc -> ops = (Operation.transfer_tokens ParamUnit amount sc) :: [] /@\label{boomerang_gospel_ensures_contract_some}@/
          | None -> true /@\label{boomerang_gospel_ensures_contract_none}@/ /@\label{boomerang_gospel_ensures_end}@/
      raises /@\label{boomerang_gospel_raises_start}@/
        Invalid_argument _ ->
          match (Contract.contract (Global.get_source env) ParamUnit) with None -> true | Some _ -> false *) /@\label{boomerang_gospel_raises_end}@/ /@\label{boomerang_gospel_end}@/
