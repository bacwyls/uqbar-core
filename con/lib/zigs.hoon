::  [UQ| DAO]
::  zigs.hoon v1.0
::
/+  *zig-sys-smart
|%
++  sur
  |%
  +$  token-metadata
    ::  will be automatically inserted into town state
    ::  at instantiation, along with this contract
    ::  hardcoded values included to match token standard
    $:  name=@t
        symbol=@t
        decimals=@ud
        supply=@ud
        cap=~  ::  no pre-set supply cap
        mintable=%.n
        minters=~
        deployer=address  ::  will be 0x0
        salt=@            ::  'zigs'
    ==
  ::
  +$  account
    $:  balance=@ud
        allowances=(pmap address @ud)
        metadata=id
        nonces=(pmap address @ud)
    ==
  ::
  +$  action
    $%  $:  %give
            budget=@ud
            to=address
            amount=@ud
            from-account=id
            to-account=(unit id)
        ==
    ::
        $:  %take
            to=address
            amount=@ud
            from-account=id
            to-account=(unit id)
        ==
    ::
        $:  %set-allowance
            who=address
            amount=@ud  ::  (to revoke, call with amount=0)
            account=id
        ==
    ==
  --
::
++  lib
  |%
  --
--
