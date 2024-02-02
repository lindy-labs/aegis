import Aegis.Commands

def fib_jumps_input : String := "{
  \"version\": 1,
  \"type_declarations\": [
    {
      \"id\": {
        \"id\": 18197987107266074389,
        \"debug_name\": \"felt252\"
      },
      \"long_id\": {
        \"generic_id\": \"felt252\",
        \"generic_args\": []
      },
      \"declared_type_info\": null
    },
    {
      \"id\": {
        \"id\": 8338741463261264245,
        \"debug_name\": \"GasBuiltin\"
      },
      \"long_id\": {
        \"generic_id\": \"GasBuiltin\",
        \"generic_args\": []
      },
      \"declared_type_info\": null
    },
    {
      \"id\": {
        \"id\": 5158587525321846130,
        \"debug_name\": \"RangeCheck\"
      },
      \"long_id\": {
        \"generic_id\": \"RangeCheck\",
        \"generic_args\": []
      },
      \"declared_type_info\": null
    },
    {
      \"id\": {
        \"id\": 12132746703728246991,
        \"debug_name\": \"NonZeroInt\"
      },
      \"long_id\": {
        \"generic_id\": \"NonZero\",
        \"generic_args\": [
          {
            \"Type\": {
              \"id\": 18197987107266074389,
              \"debug_name\": \"felt252\"
            }
          }
        ]
      },
      \"declared_type_info\": null
    }
  ],
  \"libfunc_declarations\": [
    {
      \"id\": {
        \"id\": 3328301606880823183,
        \"debug_name\": \"branch_align\"
      },
      \"long_id\": {
        \"generic_id\": \"branch_align\",
        \"generic_args\": []
      }
    },
    {
      \"id\": {
        \"id\": 5573091817713561949,
        \"debug_name\": \"felt252_add\"
      },
      \"long_id\": {
        \"generic_id\": \"felt252_add\",
        \"generic_args\": []
      }
    },
    {
      \"id\": {
        \"id\": 5747884298157259530,
        \"debug_name\": \"felt252_const_0\"
      },
      \"long_id\": {
        \"generic_id\": \"felt252_const\",
        \"generic_args\": [
          {
            \"Value\": [
              0,
              []
            ]
          }
        ]
      }
    },
    {
      \"id\": {
        \"id\": 5747885397668887741,
        \"debug_name\": \"felt252_const_1\"
      },
      \"long_id\": {
        \"generic_id\": \"felt252_const\",
        \"generic_args\": [
          {
            \"Value\": [
              1,
              [
                1
              ]
            ]
          }
        ]
      }
    },
    {
      \"id\": {
        \"id\": 3075775707538119114,
        \"debug_name\": \"felt252_const_minus_1\"
      },
      \"long_id\": {
        \"generic_id\": \"felt252_const\",
        \"generic_args\": [
          {
            \"Value\": [
              -1,
              [
                1
              ]
            ]
          }
        ]
      }
    },
    {
      \"id\": {
        \"id\": 6741348721511978627,
        \"debug_name\": \"felt252_drop\"
      },
      \"long_id\": {
        \"generic_id\": \"drop\",
        \"generic_args\": [
          {
            \"Type\": {
              \"id\": 18197987107266074389,
              \"debug_name\": \"felt252\"
            }
          }
        ]
      }
    },
    {
      \"id\": {
        \"id\": 2468470103186650467,
        \"debug_name\": \"felt252_dup\"
      },
      \"long_id\": {
        \"generic_id\": \"dup\",
        \"generic_args\": [
          {
            \"Type\": {
              \"id\": 18197987107266074389,
              \"debug_name\": \"felt252\"
            }
          }
        ]
      }
    },
    {
      \"id\": {
        \"id\": 4730041110748051225,
        \"debug_name\": \"felt252_is_zero\"
      },
      \"long_id\": {
        \"generic_id\": \"felt252_is_zero\",
        \"generic_args\": []
      }
    },
    {
      \"id\": {
        \"id\": 10451117352454336008,
        \"debug_name\": \"felt252_sub_1\"
      },
      \"long_id\": {
        \"generic_id\": \"felt252_sub_const\",
        \"generic_args\": [
          {
            \"Value\": [
              1,
              [
                1
              ]
            ]
          }
        ]
      }
    },
    {
      \"id\": {
        \"id\": 9547199891349871288,
        \"debug_name\": \"felt252_unwrap_non_zero\"
      },
      \"long_id\": {
        \"generic_id\": \"unwrap_non_zero\",
        \"generic_args\": [
          {
            \"Type\": {
              \"id\": 18197987107266074389,
              \"debug_name\": \"felt252\"
            }
          }
        ]
      }
    },
    {
      \"id\": {
        \"id\": 566598754701111445,
        \"debug_name\": \"withdraw_gas\"
      },
      \"long_id\": {
        \"generic_id\": \"withdraw_gas\",
        \"generic_args\": []
      }
    },
    {
      \"id\": {
        \"id\": 16940139219101328589,
        \"debug_name\": \"jump\"
      },
      \"long_id\": {
        \"generic_id\": \"jump\",
        \"generic_args\": []
      }
    },
    {
      \"id\": {
        \"id\": 17829783910969655620,
        \"debug_name\": \"redeposit_gas\"
      },
      \"long_id\": {
        \"generic_id\": \"redeposit_gas\",
        \"generic_args\": []
      }
    },
    {
      \"id\": {
        \"id\": 940060015955306962,
        \"debug_name\": \"rename_felt252\"
      },
      \"long_id\": {
        \"generic_id\": \"rename\",
        \"generic_args\": [
          {
            \"Type\": {
              \"id\": 18197987107266074389,
              \"debug_name\": \"felt252\"
            }
          }
        ]
      }
    },
    {
      \"id\": {
        \"id\": 16869075576697926123,
        \"debug_name\": \"revoke_ap_tracking\"
      },
      \"long_id\": {
        \"generic_id\": \"revoke_ap_tracking\",
        \"generic_args\": []
      }
    },
    {
      \"id\": {
        \"id\": 14115798396771957644,
        \"debug_name\": \"store_temp_felt252\"
      },
      \"long_id\": {
        \"generic_id\": \"store_temp\",
        \"generic_args\": [
          {
            \"Type\": {
              \"id\": 18197987107266074389,
              \"debug_name\": \"felt252\"
            }
          }
        ]
      }
    },
    {
      \"id\": {
        \"id\": 7943736942875005115,
        \"debug_name\": \"store_temp_gb\"
      },
      \"long_id\": {
        \"generic_id\": \"store_temp\",
        \"generic_args\": [
          {
            \"Type\": {
              \"id\": 8338741463261264245,
              \"debug_name\": \"GasBuiltin\"
            }
          }
        ]
      }
    },
    {
      \"id\": {
        \"id\": 7931306963920539685,
        \"debug_name\": \"store_temp_rc\"
      },
      \"long_id\": {
        \"generic_id\": \"store_temp\",
        \"generic_args\": [
          {
            \"Type\": {
              \"id\": 5158587525321846130,
              \"debug_name\": \"RangeCheck\"
            }
          }
        ]
      }
    }
  ],
  \"statements\": [
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 16869075576697926123,
          \"debug_name\": \"revoke_ap_tracking\"
        },
        \"args\": [],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": []
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 4730041110748051225,
          \"debug_name\": \"felt252_is_zero\"
        },
        \"args\": [
          {
            \"id\": 12638194897137039473,
            \"debug_name\": \"n\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": []
          },
          {
            \"target\": {
              \"Statement\": 9
            },
            \"results\": [
              {
                \"id\": 12638194897137039473,
                \"debug_name\": \"n\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 3328301606880823183,
          \"debug_name\": \"branch_align\"
        },
        \"args\": [],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": []
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 7931306963920539685,
          \"debug_name\": \"store_temp_rc\"
        },
        \"args\": [
          {
            \"id\": 638478738777676098,
            \"debug_name\": \"rc\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 638478738777676098,
                \"debug_name\": \"rc\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 17829783910969655620,
          \"debug_name\": \"redeposit_gas\"
        },
        \"args\": [
          {
            \"id\": 618457731543555724,
            \"debug_name\": \"gb\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 618457731543555724,
                \"debug_name\": \"gb\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 7943736942875005115,
          \"debug_name\": \"store_temp_gb\"
        },
        \"args\": [
          {
            \"id\": 618457731543555724,
            \"debug_name\": \"gb\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 618457731543555724,
                \"debug_name\": \"gb\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 5747885397668887741,
          \"debug_name\": \"felt252_const_1\"
        },
        \"args\": [],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 1875936269717626031,
                \"debug_name\": \"one\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 14115798396771957644,
          \"debug_name\": \"store_temp_felt252\"
        },
        \"args\": [
          {
            \"id\": 1875936269717626031,
            \"debug_name\": \"one\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 1875936269717626031,
                \"debug_name\": \"one\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Return\": [
        {
          \"id\": 638478738777676098,
          \"debug_name\": \"rc\"
        },
        {
          \"id\": 618457731543555724,
          \"debug_name\": \"gb\"
        },
        {
          \"id\": 1875936269717626031,
          \"debug_name\": \"one\"
        }
      ]
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 3328301606880823183,
          \"debug_name\": \"branch_align\"
        },
        \"args\": [],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": []
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 9547199891349871288,
          \"debug_name\": \"felt252_unwrap_non_zero\"
        },
        \"args\": [
          {
            \"id\": 12638194897137039473,
            \"debug_name\": \"n\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 12638194897137039473,
                \"debug_name\": \"n\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 14115798396771957644,
          \"debug_name\": \"store_temp_felt252\"
        },
        \"args\": [
          {
            \"id\": 12638194897137039473,
            \"debug_name\": \"n\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 12638194897137039473,
                \"debug_name\": \"n\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 7931306963920539685,
          \"debug_name\": \"store_temp_rc\"
        },
        \"args\": [
          {
            \"id\": 638478738777676098,
            \"debug_name\": \"rc\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 638478738777676098,
                \"debug_name\": \"rc\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 7943736942875005115,
          \"debug_name\": \"store_temp_gb\"
        },
        \"args\": [
          {
            \"id\": 618457731543555724,
            \"debug_name\": \"gb\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 618457731543555724,
                \"debug_name\": \"gb\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 5747885397668887741,
          \"debug_name\": \"felt252_const_1\"
        },
        \"args\": [],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 12638187200555641996,
                \"debug_name\": \"a\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 14115798396771957644,
          \"debug_name\": \"store_temp_felt252\"
        },
        \"args\": [
          {
            \"id\": 12638187200555641996,
            \"debug_name\": \"a\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 12638187200555641996,
                \"debug_name\": \"a\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 5747884298157259530,
          \"debug_name\": \"felt252_const_0\"
        },
        \"args\": [],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 12638190499090526629,
                \"debug_name\": \"b\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 14115798396771957644,
          \"debug_name\": \"store_temp_felt252\"
        },
        \"args\": [
          {
            \"id\": 12638190499090526629,
            \"debug_name\": \"b\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 12638190499090526629,
                \"debug_name\": \"b\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 4730041110748051225,
          \"debug_name\": \"felt252_is_zero\"
        },
        \"args\": [
          {
            \"id\": 12638194897137039473,
            \"debug_name\": \"n\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": []
          },
          {
            \"target\": {
              \"Statement\": 26
            },
            \"results\": [
              {
                \"id\": 12638194897137039473,
                \"debug_name\": \"n\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 3328301606880823183,
          \"debug_name\": \"branch_align\"
        },
        \"args\": [],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": []
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 6741348721511978627,
          \"debug_name\": \"felt252_drop\"
        },
        \"args\": [
          {
            \"id\": 12638190499090526629,
            \"debug_name\": \"b\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": []
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 7931306963920539685,
          \"debug_name\": \"store_temp_rc\"
        },
        \"args\": [
          {
            \"id\": 638478738777676098,
            \"debug_name\": \"rc\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 638478738777676098,
                \"debug_name\": \"rc\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 17829783910969655620,
          \"debug_name\": \"redeposit_gas\"
        },
        \"args\": [
          {
            \"id\": 618457731543555724,
            \"debug_name\": \"gb\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 618457731543555724,
                \"debug_name\": \"gb\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 7943736942875005115,
          \"debug_name\": \"store_temp_gb\"
        },
        \"args\": [
          {
            \"id\": 618457731543555724,
            \"debug_name\": \"gb\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 618457731543555724,
                \"debug_name\": \"gb\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 14115798396771957644,
          \"debug_name\": \"store_temp_felt252\"
        },
        \"args\": [
          {
            \"id\": 12638187200555641996,
            \"debug_name\": \"a\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 12638187200555641996,
                \"debug_name\": \"a\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Return\": [
        {
          \"id\": 638478738777676098,
          \"debug_name\": \"rc\"
        },
        {
          \"id\": 618457731543555724,
          \"debug_name\": \"gb\"
        },
        {
          \"id\": 12638187200555641996,
          \"debug_name\": \"a\"
        }
      ]
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 3328301606880823183,
          \"debug_name\": \"branch_align\"
        },
        \"args\": [],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": []
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 9547199891349871288,
          \"debug_name\": \"felt252_unwrap_non_zero\"
        },
        \"args\": [
          {
            \"id\": 12638194897137039473,
            \"debug_name\": \"n\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 12638194897137039473,
                \"debug_name\": \"n\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 566598754701111445,
          \"debug_name\": \"withdraw_gas\"
        },
        \"args\": [
          {
            \"id\": 638478738777676098,
            \"debug_name\": \"rc\"
          },
          {
            \"id\": 618457731543555724,
            \"debug_name\": \"gb\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 638478738777676098,
                \"debug_name\": \"rc\"
              },
              {
                \"id\": 618457731543555724,
                \"debug_name\": \"gb\"
              }
            ]
          },
          {
            \"target\": {
              \"Statement\": 40
            },
            \"results\": [
              {
                \"id\": 638478738777676098,
                \"debug_name\": \"rc\"
              },
              {
                \"id\": 618457731543555724,
                \"debug_name\": \"gb\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 3328301606880823183,
          \"debug_name\": \"branch_align\"
        },
        \"args\": [],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": []
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 2468470103186650467,
          \"debug_name\": \"felt252_dup\"
        },
        \"args\": [
          {
            \"id\": 12638187200555641996,
            \"debug_name\": \"a\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 12638187200555641996,
                \"debug_name\": \"a\"
              },
              {
                \"id\": 5124477032042102868,
                \"debug_name\": \"prev_a\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 5573091817713561949,
          \"debug_name\": \"felt252_add\"
        },
        \"args\": [
          {
            \"id\": 12638187200555641996,
            \"debug_name\": \"a\"
          },
          {
            \"id\": 12638190499090526629,
            \"debug_name\": \"b\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 12638187200555641996,
                \"debug_name\": \"a\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 940060015955306962,
          \"debug_name\": \"rename_felt252\"
        },
        \"args\": [
          {
            \"id\": 5124477032042102868,
            \"debug_name\": \"prev_a\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 12638190499090526629,
                \"debug_name\": \"b\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 10451117352454336008,
          \"debug_name\": \"felt252_sub_1\"
        },
        \"args\": [
          {
            \"id\": 12638194897137039473,
            \"debug_name\": \"n\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 12638194897137039473,
                \"debug_name\": \"n\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 14115798396771957644,
          \"debug_name\": \"store_temp_felt252\"
        },
        \"args\": [
          {
            \"id\": 12638194897137039473,
            \"debug_name\": \"n\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 12638194897137039473,
                \"debug_name\": \"n\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 7931306963920539685,
          \"debug_name\": \"store_temp_rc\"
        },
        \"args\": [
          {
            \"id\": 638478738777676098,
            \"debug_name\": \"rc\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 638478738777676098,
                \"debug_name\": \"rc\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 7943736942875005115,
          \"debug_name\": \"store_temp_gb\"
        },
        \"args\": [
          {
            \"id\": 618457731543555724,
            \"debug_name\": \"gb\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 618457731543555724,
                \"debug_name\": \"gb\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 14115798396771957644,
          \"debug_name\": \"store_temp_felt252\"
        },
        \"args\": [
          {
            \"id\": 12638187200555641996,
            \"debug_name\": \"a\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 12638187200555641996,
                \"debug_name\": \"a\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 14115798396771957644,
          \"debug_name\": \"store_temp_felt252\"
        },
        \"args\": [
          {
            \"id\": 12638190499090526629,
            \"debug_name\": \"b\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 12638190499090526629,
                \"debug_name\": \"b\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 16940139219101328589,
          \"debug_name\": \"jump\"
        },
        \"args\": [],
        \"branches\": [
          {
            \"target\": {
              \"Statement\": 18
            },
            \"results\": []
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 3328301606880823183,
          \"debug_name\": \"branch_align\"
        },
        \"args\": [],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": []
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 6741348721511978627,
          \"debug_name\": \"felt252_drop\"
        },
        \"args\": [
          {
            \"id\": 12638187200555641996,
            \"debug_name\": \"a\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": []
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 6741348721511978627,
          \"debug_name\": \"felt252_drop\"
        },
        \"args\": [
          {
            \"id\": 12638190499090526629,
            \"debug_name\": \"b\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": []
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 6741348721511978627,
          \"debug_name\": \"felt252_drop\"
        },
        \"args\": [
          {
            \"id\": 12638194897137039473,
            \"debug_name\": \"n\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": []
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 7931306963920539685,
          \"debug_name\": \"store_temp_rc\"
        },
        \"args\": [
          {
            \"id\": 638478738777676098,
            \"debug_name\": \"rc\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 638478738777676098,
                \"debug_name\": \"rc\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 17829783910969655620,
          \"debug_name\": \"redeposit_gas\"
        },
        \"args\": [
          {
            \"id\": 618457731543555724,
            \"debug_name\": \"gb\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 618457731543555724,
                \"debug_name\": \"gb\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 7943736942875005115,
          \"debug_name\": \"store_temp_gb\"
        },
        \"args\": [
          {
            \"id\": 618457731543555724,
            \"debug_name\": \"gb\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 618457731543555724,
                \"debug_name\": \"gb\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 3075775707538119114,
          \"debug_name\": \"felt252_const_minus_1\"
        },
        \"args\": [],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 14050392017135853004,
                \"debug_name\": \"err\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Invocation\": {
        \"libfunc_id\": {
          \"id\": 14115798396771957644,
          \"debug_name\": \"store_temp_felt252\"
        },
        \"args\": [
          {
            \"id\": 14050392017135853004,
            \"debug_name\": \"err\"
          }
        ],
        \"branches\": [
          {
            \"target\": \"Fallthrough\",
            \"results\": [
              {
                \"id\": 14050392017135853004,
                \"debug_name\": \"err\"
              }
            ]
          }
        ]
      }
    },
    {
      \"Return\": [
        {
          \"id\": 638478738777676098,
          \"debug_name\": \"rc\"
        },
        {
          \"id\": 618457731543555724,
          \"debug_name\": \"gb\"
        },
        {
          \"id\": 14050392017135853004,
          \"debug_name\": \"err\"
        }
      ]
    }
  ],
  \"funcs\": [
    {
      \"id\": {
        \"id\": 2313213558037562915,
        \"debug_name\": \"Fibonacci\"
      },
      \"signature\": {
        \"param_types\": [
          {
            \"id\": 5158587525321846130,
            \"debug_name\": \"RangeCheck\"
          },
          {
            \"id\": 8338741463261264245,
            \"debug_name\": \"GasBuiltin\"
          },
          {
            \"id\": 18197987107266074389,
            \"debug_name\": \"felt252\"
          }
        ],
        \"ret_types\": [
          {
            \"id\": 5158587525321846130,
            \"debug_name\": \"RangeCheck\"
          },
          {
            \"id\": 8338741463261264245,
            \"debug_name\": \"GasBuiltin\"
          },
          {
            \"id\": 18197987107266074389,
            \"debug_name\": \"felt252\"
          }
        ]
      },
      \"params\": [
        {
          \"id\": {
            \"id\": 638478738777676098,
            \"debug_name\": \"rc\"
          },
          \"ty\": {
            \"id\": 5158587525321846130,
            \"debug_name\": \"RangeCheck\"
          }
        },
        {
          \"id\": {
            \"id\": 618457731543555724,
            \"debug_name\": \"gb\"
          },
          \"ty\": {
            \"id\": 8338741463261264245,
            \"debug_name\": \"GasBuiltin\"
          }
        },
        {
          \"id\": {
            \"id\": 12638194897137039473,
            \"debug_name\": \"n\"
          },
          \"ty\": {
            \"id\": 18197987107266074389,
            \"debug_name\": \"felt252\"
          }
        }
      ],
      \"entry_point\": 0
    }
  ]
}"

def foo :=
  match Lean.Json.parse fib_jumps_input with
  | .ok j => Sierra.parseJson j
  | .error e => throwError e

open Sierra Lean Meta

def analyzeFile' (s : String) (idx : ℕ := 0) : Lean.MetaM Format := do
  let .ok j := Lean.Json.parse fib_jumps_input
    | throwError "foo"
  let sf ← Sierra.parseJson j
  let ⟨ident, pc, inputArgs, outputTypes⟩ := sf.declarations.get! idx
  let e ← getFuncCondition sf ∅ ident pc inputArgs outputTypes
  let esType ← inferType e
  return (← ppExpr e) ++ "\n Inferred Type:" ++ (← ppExpr esType)

#eval analyzeFile' fib_jumps_input

#eval foo
