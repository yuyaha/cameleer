
type config =
  { title          : string
  ; beginning_time : timestamp
  ; finish_time    : timestamp
  }

type action =
  | Vote of string
  | Init of config

type storage =
  { config     : config
  ; candidates : (string, int) map
  ; voters     : address set
  }

let [@logic] init (conf : config) =
  { config = conf
  ; candidates = Map [ ("Yes", 0); ("No", 0) ]
  ; voters     = Set []
  }

let vote (env : Env.t) (name : string) (storage : storage) =
  let now = Global.get_now env in

  if (Timestamp.le storage.config.beginning_time now && Timestamp.lt now storage.config.finish_time) then () else raise Assert_failure;

  let addr = Global.get_source env in

  if (Set.mem addr storage.voters) then raise Assert_failure else ();

  let x = match Map.get String.eq name storage.candidates with
    | Some i -> i
    | None -> 0
  in
  ([] : operation list),
  { config = storage.config
  ; candidates = Map.update String.eq String.lt name (Some (x + 1)) storage.candidates
  ; voters = Set.update Address.eq Address.lt addr true storage.voters
  }
(*@ ops, stg = vote env name storage
    ensures
      let now = Global.get_now env in
      Timestamp.le storage.config.beginning_time now &&
      Timestamp.lt now storage.config.finish_time &&
      not Set.mem (Global.get_source env) storage.voters ->
      forall nm. match (Map.get String.eq nm stg.candidates) with
      | Some _ -> true
      | None -> false
      -> match (Map.get String.eq nm storage.candidates), (Map.get String.eq nm stg.candidates) with
      | Some pv, Some cv ->
        if String.eq name nm then pv + 1 = cv else pv = cv
      | None, Some cv -> String.eq name nm && cv = 1
      | _, _ -> false
    raises
      Assert_failure ->
        let now = Global.get_now env in
        not ( Timestamp.le storage.config.beginning_time now &&
            Timestamp.lt now storage.config.finish_time &&
            not Set.mem (Global.get_source env) storage.voters ) *)
