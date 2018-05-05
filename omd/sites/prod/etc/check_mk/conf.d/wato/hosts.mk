# Created by WATO
# encoding: utf-8

all_hosts += [
  "control1.gate.rtf|lan|ip-v4|cmk-agent|site:prod|tcp|ip-v4-only|prod|wato|/" + FOLDER_PATH + "/",
  "control2.gate.rtf|lan|ip-v4|cmk-agent|site:prod|tcp|ip-v4-only|prod|wato|/" + FOLDER_PATH + "/",
  "mgen1.gate.rtf|lan|ip-v4|cmk-agent|site:prod|tcp|ip-v4-only|prod|wato|/" + FOLDER_PATH + "/",
  "mgen2.gate.rtf|lan|ip-v4|cmk-agent|site:prod|tcp|ip-v4-only|prod|wato|/" + FOLDER_PATH + "/",
  "pgen1.gate.rtf|lan|ip-v4|cmk-agent|site:prod|tcp|ip-v4-only|prod|wato|/" + FOLDER_PATH + "/",
  "pgen2.gate.rtf|lan|ip-v4|cmk-agent|site:prod|tcp|ip-v4-only|prod|wato|/" + FOLDER_PATH + "/",
]


# Host attributes (needed for WATO)
host_attributes.update(
{'control1.gate.rtf': {},
 'control2.gate.rtf': {},
 'mgen1.gate.rtf': {},
 'mgen2.gate.rtf': {},
 'pgen1.gate.rtf': {},
 'pgen2.gate.rtf': {}})
