<?php
// Created by WATO
global $mk_hosttags, $mk_auxtags;
$mk_hosttags = array(
    'networking' => array(
        null,
        'Networking Segment',
        array(
            'wan' => array(
                'WAN (high latency)',
                array(
                ),
            ),
            'lan' => array(
                'Local network (low latency)',
                array(
                ),
            ),
            'dmz' => array(
                'DMZ (low latency, secure access)',
                array(
                ),
            ),
        ),
    ),
    'criticality' => array(
        null,
        'Criticality',
        array(
            'test' => array(
                'Test system',
                array(
                ),
            ),
            'offline' => array(
                'Do not monitor this host',
                array(
                ),
            ),
            'prod' => array(
                'Productive system',
                array(
                ),
            ),
            'critical' => array(
                'Business critical',
                array(
                ),
            ),
        ),
    ),
    'agent' => array(
        null,
        'Agent type',
        array(
            'cmk-agent' => array(
                'Check_MK Agent (Server)',
                array(
                    'tcp',
                ),
            ),
            'ping' => array(
                'No Agent',
                array(
                ),
            ),
            'snmp-only' => array(
                'SNMP (Networking device, Appliance)',
                array(
                    'snmp',
                ),
            ),
            'snmp-tcp' => array(
                'Dual: Check_MK Agent + SNMP',
                array(
                    'snmp',
                    'tcp',
                ),
            ),
            'snmp-v1' => array(
                'Legacy SNMP device (using V1)',
                array(
                    'snmp',
                ),
            ),
        ),
    ),
);
$mk_auxtags = array(
    'snmp' => 'monitor via SNMP',
    'tcp' => 'monitor via Check_MK Agent',
);

function taggroup_title($group_id) {
    global $mk_hosttags;
    if (isset($mk_hosttags[$group_id]))
        return $mk_hosttags[$group_id][0];
    else
        return $taggroup;
}

function taggroup_choice($group_id, $object_tags) {
    global $mk_hosttags;
    if (!isset($mk_hosttags[$group_id]))
        return false;
    foreach ($object_tags AS $tag) {
        if (isset($mk_hosttags[$group_id][2][$tag])) {
            // Found a match of the objects tags with the taggroup
            // now return an array of the matched tag and its alias
            return array($tag, $mk_hosttags[$group_id][2][$tag][0]);
        }
    }
    // no match found. Test whether or not a "None" choice is allowed
    if (isset($mk_hosttags[$group_id][2][null]))
        return array(null, $mk_hosttags[$group_id][2][null][0]);
    else
        return null; // no match found
}

function all_taggroup_choices($object_tags) {
    global $mk_hosttags;
    $choices = array();
    foreach ($mk_hosttags AS $group_id => $group) {
        $choices[$group_id] = array(
            'topic' => $group[0],
            'title' => $group[1],
            'value' => taggroup_choice($group_id, $object_tags),
        );
    }
    return $choices;
}

?>
