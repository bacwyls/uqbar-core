|%
++  interface-json
  |^  ^-  (map @tas json)
  %-  ~(gas by *(map @tas json))
  :+  [%deploy (need (de-json:html deploy-cord))]
    [%upgrade (need (de-json:html upgrade-cord))]
  ~
  ::
  ++  deploy-cord
    ^-  cord
    '''
    [
      {"mutable": "?"},
      {
        "cont": [
          {"bat": "*"},
          {"pay": "*"}
        ]
      },
      {"interface": ["map", "tas", "json"]},
      {"types": ["map", "tas", "json"]}
    ]
    '''
  ::
  ++  upgrade-cord
    ^-  cord
    '''
    [
      {"to-update": "ux"},
      {
        "new-nok": [
          {"bat": "*"},
          {"pay": "*"}
        ]
      }
    ]
    '''
  --
--
