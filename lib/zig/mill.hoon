/+  *bink, tiny
|_  [validator-id=@ux =land:tiny now=time]
::
::  +mill-all: mills all calls in mempool
::
++  mill-all
  |=  [helix-id=@ud =town:tiny mempool=(list call:tiny)]
  =/  pending
    %+  sort  mempool
    |=  [a=call:tiny b=call:tiny]
    (gth rate.a rate.b)
  =|  result=(list [@ux call:tiny])
          ::  'chunk' def
  |-  ^-  [(list [@ux call:tiny]) town:tiny]
  ?~  pending
    [result town]
  %_  $
    pending  t.pending
    result   [[`@ux`(shax (jam i.pending)) i.pending] result]
    town  (mill helix-id town i.pending)
  ==
::  +mill: processes a single call and returns updated town
::
++  mill
  |=  [town-id=@ud =town:tiny =call:tiny]
  ^-  town:tiny
  ?.  ?=(user:tiny from.call)  town
  ?~  curr-nonce=(~(get by q.town) id.from.call)
    town  ::  missing user
  ?.  =(nonce.from.call +(u.curr-nonce))
    town  ::  bad nonce
  ?.  (~(audit tax p.town) call)
    town  ::  can't afford gas
  =+  [gan rem]=(~(work farm p.town) call)
  =/  fee=@ud   (sub budget.call rem)
  :-  ?~  gan  (~(pay tax p.town) id.from.call fee)
      (~(pay tax u.gan) id.from.call fee)
  (~(put by q.town) id.from.call nonce.from.call)
::
::  +tax: manage payment for contract execution in zigs
::
++  tax
  |_  =granary:tiny
  +$  zigs-mold
    $:  total=@ud
        balances=(map id:tiny @ud)
        allowances=(map [owner=id:tiny sender=id:tiny] @ud)
        coinbase-rate=@ud
    ==
  ::  +audit: evaluate whether a caller can afford gas
  ++  audit
    |=  =call:tiny
    ^-  ?
    ?~  zigs=(~(get by granary) zigs-rice-id:tiny)  %.n
    ?.  ?=(%& -.germ.u.zigs)                        %.n
    =/  data  ;;(zigs-mold data.p.germ.u.zigs)
    ?.  ?=(user:tiny from.call)                     %.n
    ?~  bal=(~(get by balances.data) id.from.call)  %.n
    (gth u.bal (mul rate.call budget.call))
  ::  +pay: extract gas fee from caller's zigs balance
  ++  pay
    |=  [payee=id:tiny fee=@ud]
    ^-  granary:tiny
    ?~  zigs=(~(get by granary) zigs-rice-id:tiny)  granary
    ?.  ?=(%& -.germ.u.zigs)                        granary
    =/  data  ;;(zigs-mold data.p.germ.u.zigs)
    =.  balances.data
      %+  %~  jab  by
          ?.  (~(has by balances.data) validator-id)
            ::  make account if none in balances
            (~(put by balances.data) validator-id fee)
          ::  otherwise add to existing balance
          %+  ~(jab by balances.data)
            validator-id
          |=(bal=@ud (add bal fee))
        payee
      |=(bal=@ud (sub bal fee))
    =.  data.p.germ.u.zigs  data
    (~(put by granary) zigs-rice-id:tiny u.zigs)
  --
::
::  +farm: execute a call to a contract within a wheat
::
++  farm
  |_  =granary:tiny
  ::
  ++  work
    |=  =call:tiny
    ^-  [(unit granary:tiny) @ud]
    =/  crop  (plant call(budget (div budget.call rate.call)))
    :_  +.crop
    ?~  -.crop  ~
    (harvest u.-.crop to.call from.call)
  ::
  ++  plant
    |=  =call:tiny
    ^-  [(unit contract-result:tiny) @ud]
    |^
    =/  args  (fertilize args.call)
    ?~  con=(germinate to.call)
      `budget.call
    (grow u.con args call)
    ::
    ++  fertilize
      |=  arg=call-args:tiny
      ^-  contract-args:tiny
      =*  inp  +.arg
      :-  -.arg
      :+  caller.inp
        args.inp
      %-  ~(gas by *contract-input-rice:tiny)
      %+  murn  ~(tap in rice-ids.inp)
      |=  =id:tiny
      ?~  res=(~(get by granary) id)  ~
      ?.  ?=(%& -.germ.u.res)  ~
      `[id u.res]
    ::
    ++  germinate
      |=  find=id:tiny
      ^-  (unit contract:tiny)
      ?~  gra=(~(get by granary) find)  ~
      ?.  ?=(%| -.germ.u.gra)  ~
      ?~  p.germ.u.gra  ~
      `!<(contract:tiny [-:!>(*contract:tiny) u.p.germ.u.gra])
    --
  ::
  ++  grow
    |=  [cont=contract:tiny args=contract-args:tiny =call:tiny]
    ^-  [(unit contract-result:tiny) @ud]
    |^
    =+  [bran rem]=(weed cont to.call args ~ budget.call)
    ?:  ?=(%& -.bran)
      p.bran^rem
    |-
    =*  next  next.p.bran
    =*  mem   mem.p.bran
    =^  crop  rem
      (plant call(from to.call, to to.next, budget rem, args args.next))
    ?~  crop  `rem
    =/  gan  (harvest u.crop to.call from.call)
    ?~  gan  `rem
    =.  granary  u.gan
    =^  eve  rem
      (weed cont to.call [%event u.crop] mem rem)
    ?:  ?=(%& -.eve)
      p.eve^rem
    %_  $
      next.p.bran  next.p.eve
      mem.p.bran   mem.p.eve
    ==
    ::
    ++  weed
      |=  [cont=contract:tiny to=id:tiny args=contract-args:tiny mem=(unit vase) budget=@ud]
      ^-  [(each (unit contract-result:tiny) continuation:tiny) @ud]
      =+  [res bud]=(barn cont to args ~ budget)
      ?~  res             [%& ~]^bud
      ?:  ?=(%| -.u.res)  [%& ~]^bud
      ?:  ?=(%result -.p.u.res)
        ?.  ?|  &(?=(%read -.p.p.u.res) ?=(%read -.args))
                &(?=(%write -.p.p.u.res) ?=(%write -.args))
            ==
          [%& ~]^bud
        [%& `p.p.u.res]^bud
      [%| p.p.u.res]^bud
    ::
    ::  +barn: run contract formula with arguments and memory, bounded by bud
    ::
    ++  barn
      |=  [=contract:tiny to=id:tiny args=contract-args:tiny mem=(unit vase) bud=@ud]
      ^-  [(unit (each contract-output:tiny (list tank))) @ud]
      %+  bull
        ?-  -.args
          %read   |.(;;(contract-output:tiny (~(read contract mem to) +.args)))
          %write  |.(;;(contract-output:tiny (~(write contract mem to) +.args)))
          %event  |.(;;(contract-output:tiny (~(event contract mem to) +.args)))
        ==
      bud
    --
  ::
  ++  harvest
    |=  [res=contract-result:tiny lord=id:tiny from=caller:tiny]
    ^-  (unit granary:tiny)
    ?:  ?=(%read -.res)  `granary
    =-  ?.  -  ~
        `(~(uni by granary) (~(uni by changed.res) issued.res))
    ?&  %-  ~(all in changed.res)
        |=  [=id:tiny =grain:tiny]
        ::  id in changed map must be equal to id in grain AND
        ::  all changed grains must already exist AND
        ::  no changed grains may also have been issued at same time AND
        ::  only grains that proclaim us lord may be changed
        ?&  =(id id.grain)
            (~(has by granary) id.grain)
            !(~(has by issued.res) id.grain)
            =(lord lord:(~(got by granary) id))
        ==
      ::
        %-  ~(all in issued.res)
        |=  [=id:tiny =grain:tiny]
        ::  id in issued map must be equal to id in grain AND
        ::  all newly issued grains must not already exist
        ?&  =(id id.grain)
            !(~(has by granary) id.grain)
            =(lord lord.grain)
    ==  ==
  --
--
