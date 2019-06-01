import json
import sys


def load_quorum_definitions(input):
    return json.load(input)

def store_quorum_definitions(data, output):
    json.dump(data, output)

def is_quorum_config_sane(q_set):
    return len(q_set['validators']) + len(q_set['innerQuorumSets']) >= q_set['threshold']

def fix_configuration(config):
    return [node for node in config if is_quorum_config_sane(node['quorumSet'])]

if __name__ == "__main__":
    data = load_quorum_definitions(sys.stdin)
    data = fix_configuration(data)
    store_quorum_definitions(data, sys.stdout)
