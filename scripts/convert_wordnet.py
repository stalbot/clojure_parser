from collections import defaultdict
import json
import os
import re

from nltk.corpus import wordnet as wn
from nltk.corpus.reader.wordnet import VERB_FRAME_STRINGS
from nltk.corpus.reader.wordnet import Synset, Lemma


SYNSET_INFO_ATTRS = [
    'also_sees',
    'attributes',
    'causes',
    'definition',
    'entailments',
    'examples',
    'frame_ids',
    'hypernyms',
    'hyponyms',
    'instance_hypernyms',
    'instance_hyponyms',
    'lexname',
    'member_holonyms',
    'member_meronyms',
    'offset',
    'part_holonyms',
    'part_meronyms',
    'pos',
    'region_domains',
    'similar_tos',
    'substance_holonyms',
    'substance_meronyms',
    'topic_domains',
    'usage_domains',
    'verb_groups'
]

LEMMA_INFO_ATTRS = [
    'also_sees',
    'antonyms',
    'attributes',
    'causes',
    'count',
    'derivationally_related_forms',
    'entailments',
    'frame_ids',
    'frame_strings',
    'hypernyms',
    'hyponyms',
    'instance_hypernyms',
    'instance_hyponyms',
    'lang',
    'member_holonyms',
    'member_meronyms',
    'name',
    'part_holonyms',
    'part_meronyms',
    'pertainyms',
    'region_domains',
    'similar_tos',
    'substance_holonyms',
    'substance_meronyms',
    'syntactic_marker',
    'topic_domains',
    'usage_domains',
    'verb_groups',
]


FSTR_REG = re.compile(r'''
                      (?P<subj>\S+)\s+
                      \%s
                      (?:\s+(?P<obj>\S+))?
                      (?:\s+(?P<ind_obj>\S+))?
                      ''', re.VERBOSE)


PREPOSITIONS = {'of', 'by', 'to', 'with', 'on', 'of'}


def extract_features_from_fstr(fstr):
    fstr = fstr.lower()
    match = FSTR_REG.match(fstr)
    if not match:
        return {}
    features = {}
    gdict = match.groupdict()
    if not gdict['obj']:
        features['trans'] = False
    elif not gdict['ind_obj']:
        features['trans'] = True
    elif gdict['obj'] not in PREPOSITIONS:
        features['trans'] = 'ditrans'
    return features


V_FEATURES_BY_FID = dict(
    ((i + 1, extract_features_from_fstr(fstr))
     for i, fstr in enumerate(VERB_FRAME_STRINGS[1:]))
)


def _transform(data):
    if isinstance(data, list) and data:
        if isinstance(data[0], Synset):
            return [s.name() for s in data]
        elif isinstance(data[0], Lemma):
            return ['.'.join((l.synset().name(), l.name())) for l in data]
    return data

ENDINGS_ALTERNATIVES = {
    's': ['es'],
    'ed': ['d', '+ed'],
    'est': ['-iest'],
    'er': ['-ier'],
    'ing': ['-ing', '+ing'],
    'en': ['ed', 'd', '+ed'],  # A trick! fall back to normal past if we can't find special
}

DEFAULT_FEAUTRES_BY_POS = {
    'v': {'person': 3, 'tense': 'present', 'plural': True},
    'n': {'person': 3, 'plural': False},
    'r': {},
    'a': {}
}
DEFAULT_FEAUTRES_BY_POS['s'] = DEFAULT_FEAUTRES_BY_POS['a']

ENDINGS_FEATURES_BY_POS = {
    'v': {
        'ing': {'tense': 'present_part', 'plural': None},
        'ed': {'tense': 'past', 'plural': None},
        'en': {'tense': 'past_part', 'plural': None},
        's': {'plural': False}
    },
    'n': {'s': {'plural': True}},
    'a': {
        'est': {'type': 'superlative'},
        'er': {'type': 'comparative'},
    },
    'r': {},
}

ENDINGS_FEATURES_BY_POS['s'] = ENDINGS_FEATURES_BY_POS['a']
DASH_FINDER = re.compile(r'([\-\+]+).*')

def is_actual_word(maybe_word, syn_name, all_words):
    return (maybe_word.lower() in all_words and
            syn_name in map(lambda x: x.name(), wn.synsets(maybe_word)))

def find_alt_stems(synset, lemma_info, all_words):
    other_endings = ENDINGS_FEATURES_BY_POS[synset.pos()]
    default_features = DEFAULT_FEAUTRES_BY_POS[synset.pos()]
    lem_name = lemma_info['name']
    syn_name = synset.name()

    found = []

    for ending, features in other_endings.items():
        found_new_word = None
        maybe_word = lem_name + ending
        if is_actual_word(maybe_word, syn_name, all_words):
            found_new_word = maybe_word
        else:
            for alt_end in ENDINGS_ALTERNATIVES[ending]:
                matched_changes = DASH_FINDER.match(alt_end)
                if matched_changes and matched_changes.groups()[0] == '-':
                    num_deletes = len(matched_changes.groups()[0])
                    maybe_word = lem_name[:-num_deletes] + alt_end[num_deletes:]
                elif matched_changes and matched_changes.groups()[0] == '+':
                    num_repeats = len(matched_changes.groups()[0])
                    maybe_word = (lem_name +
                                    ''.join(lem_name[-1] for _ in range(num_repeats)) +
                                    alt_end[num_repeats:])
                if is_actual_word(maybe_word, syn_name, all_words):
                    found_new_word = maybe_word
                    break

        if not found_new_word:
            continue

        full_features = default_features.copy()
        full_features.update(features)

        lemma_info_w_features = lemma_info.copy()
        lemma_info_w_features['features'] = full_features
        lemma_info_w_features['name'] = found_new_word

        found.append((found_new_word, lemma_info_w_features))

    return found


def transform_synset(synset, all_words):
    info = {}
    for attr in SYNSET_INFO_ATTRS:
        data = getattr(synset, attr)()
        if data:
            info[attr] = _transform(data)
    if synset.pos() == 'v':
        # Don't know how to handle more than one frame id right now
        info['features'] = V_FEATURES_BY_FID[synset.frame_ids()[0]]
    info['lemmas'] = {}
    for lemma in synset.lemmas():
        lemma_info = {}
        for attr in LEMMA_INFO_ATTRS:
            data = getattr(lemma, attr)()
            if data and (attr not in info or data != info[attr]):
                lemma_info[attr] = _transform(data)
        lemma_info['features'] = DEFAULT_FEAUTRES_BY_POS[synset.pos()]
        info['lemmas'][lemma_info['name']] = lemma_info
        for name, lemma_info in find_alt_stems(synset, lemma_info, all_words):
            info['lemmas'][name] = lemma_info
    # lemmas
    # name
    # pos
    # WTF is offset?
    return info


def main(target_dir):
    if not os.path.isdir(target_dir):
        os.mkdir(target_dir)

    with open('resources/english_wordlist.txt') as f:
        all_words = set((l.strip() for l in f.readlines()))

    by_pos = defaultdict(lambda: defaultdict(list))
    for i, s in enumerate(wn.all_synsets()):
        s_name = s.name()
        by_pos[s.pos()][s_name[0]].append(s)

    for pos, s_for_pos in by_pos.items():
        pos_dir = os.path.join(target_dir, pos)
        if not os.path.isdir(pos_dir):
            os.mkdir(pos_dir)
        for start_letter, synsets in s_for_pos.items():
            print("Doing letter {} for pos {}".format(start_letter, pos))
            synset_infos = {s.name(): transform_synset(s, all_words) for s in synsets}
            if start_letter.startswith("."):
                print("Dot start letter for syn {}".format(list(synset_infos.values())[0]))
                start_letter = "__"
            with open(os.path.join(pos_dir, start_letter + '.json'), 'w') as f:
                f.write(json.dumps(synset_infos, indent=4, sort_keys=True))


if __name__ == '__main__':
    main('resources/wordnet_as_json')
