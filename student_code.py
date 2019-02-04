import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])

        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """

        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []



    def kb_retract(self, fact):
        """Retract a fact from the KB

        Pseudo:
            if it's indeed a fact:
                find the fact in the db it wants us to remove.
                Add it to the queue

            while queue is not empty
                curr = pop the queue
                if curr is unsupported, remove it from the db
                for every supported fact and rule, remove it's pair from the supported_by,
                    then append these supported facts and rules to the queue.

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact])
        ####################################################
        # Student code goes here

        queue = []

        # find the fact
        if type(fact) == Fact:
            for a_fact in self.facts:
                if match(a_fact.statement, fact.statement, None):
                    print("found", a_fact)
                    queue.append(a_fact)

        while len(queue) > 0:
            curr = queue.pop(0)
            # if curr not supported
            if len(curr.supported_by) == 0:
                if type(curr) == Fact:
                    self.facts.remove(curr)
                else:
                    self.rules.remove(curr)

                for supported_fact in curr.supports_facts:
                    queue.append(supported_fact)
                    for fact_rule_pair in supported_fact.supported_by:
                        if curr in fact_rule_pair:
                            supported_fact.supported_by.remove(fact_rule_pair)

                for supported_rule in curr.supports_rules:
                    queue.append(supported_rule)
                    for fact_rule_pair in supported_rule.supported_by:
                        if curr in fact_rule_pair:
                            supported_rule.supported_by.remove(fact_rule_pair)
            else:
                print("Attempt to remove supported fact|rule", curr)



class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here

        bindings = match(rule.lhs[0], fact.statement, None)

        if bindings:
            # make new rule here paired with bindings for the match
            if len(rule.lhs) == 1:
                #new fact... then assert it
                newfact = Fact(instantiate(rule.rhs, bindings), [[fact, rule]])
                fact.supports_facts.append(newfact)
                rule.supports_facts.append(newfact)
                kb.kb_assert(newfact)
            else:
                right = instantiate(rule.rhs, bindings)
                left = []

                for lrulestatement in rule.lhs:
                    left.append(instantiate(lrulestatement, bindings))
                # we remove the first item of the lhs because that's what we inferred the new rule from, so we know that
                # condition will always be satisfied.
                del left[0]

                newrule = Rule([left, right], [[fact, rule]])
                fact.supports_rules.append(newrule)
                rule.supports_rules.append(newrule)
                kb.kb_assert(newrule)
        else:
            return None