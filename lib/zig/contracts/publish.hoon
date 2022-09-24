::  publish.hoon  [UQ| DAO]
::
::  Smart contract that processes deployment and upgrades
::  for other smart contracts. Automatically (?) inserted
::  on any town that wishes to allow contract production.
::
::  /+  *zig-sys-smart
/=  pub  /lib/zig/contracts/lib/publish
|_  =cart
++  write
  |=  act=action:pub
  ^-  chick
  ?-    -.act
      %deploy
    =/  lord=id  ?:(mutable.act me.cart 0x0)
    =/  contract=grain
      :*  %|
          `cont.act
          interface.act
          types.act
          (fry-wheat lord id.from.cart town-id.cart `cont.act)
          lord
          id.from.cart
          town-id.cart
      ==
    (result ~ [contract ~] ~ ~)
  ::
      %upgrade
    ::  publish contract must be lord to upgrade,
    ::  caller must be holder
    =/  contract  (need (scry to-upgrade.act))
    ?>  ?&  ?=(%| -.contract)
            =(lord.p.contract me.cart)
            =(holder.p.contract id.from.cart)
        ==
    =.  cont.p.contract  `new-nok.act
    (result [contract ~] ~ ~ ~)
  ==
::
++  read
  |_  =path
  ++  json
    ~
  ++  noun
    ~
  --
--
