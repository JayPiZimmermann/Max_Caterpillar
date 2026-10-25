#!/usr/bin/env python3
"""Exact modular evaluator caching repeated rational terms at one point.

Useful when a whole matrix row evaluates many orbit columns with shared
denominators. This changes no formulas, points, or arithmetic field.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib, json, random

HERE = Path(__file__).parent


class Evaluator:
    def __init__(self):
        self.point = None
        self.terms = {}
        self.forms = {}
        self.coefficients = {}
        self.prime = None

    def __call__(self, expression, point, prime=1000003):
        point = tuple(point)
        if (point, prime) != (self.point, self.prime):
            if prime != self.prime:
                self.coefficients.clear()
            self.point, self.prime = point, prime
            self.terms.clear()
            self.forms.clear()

        def value(form):
            if form not in self.forms:
                self.forms[form] = (sum(a*b for a, b in zip(form[:-1], point))+form[-1]) % prime
            return self.forms[form]

        total = 0
        for key, coefficient in expression.items():
            if key not in self.terms:
                numerator, power, denominator = key
                term = pow(value(numerator), power, prime)
                for form, multiplicity in denominator:
                    q = value(form)
                    if not q:
                        raise ZeroDivisionError
                    term = term*pow(pow(q, multiplicity, prime), -1, prime) % prime
                self.terms[key] = term
            if coefficient not in self.coefficients:
                self.coefficients[coefficient] = (coefficient.numerator*
                    pow(coefficient.denominator, -1, prime)) % prime
            total = (total+self.coefficients[coefficient]*self.terms[key]) % prime
        return total


def main():
    import overnight_upper_product_family as base
    import overnight_upper_triangle_attachments as attachment
    import overnight_upper_triangle_fixed as fixed
    base.group = fixed.group
    base.raw_chain = attachment.raw_chain
    witness = json.loads((HERE/'overnight_upper_two_page_witness_6.json').read_text())
    columns = [base.expression(base.sym_chain(6, item['descriptor'])) for item in witness['selected']]
    rng = random.Random(251036)
    cached = Evaluator()
    checks = 0
    for prime in (1000003, 1000000007):
        for _ in range(3):
            point = tuple(rng.randrange(1, 1000) for _ in range(4))
            for column in columns:
                for expression in column.values():
                    try:
                        expected = base.evaluate(expression, point, prime)
                    except ZeroDivisionError:
                        try:
                            cached(expression, point, prime)
                        except ZeroDivisionError:
                            continue
                        raise AssertionError('pole mismatch')
                    assert cached(expression, point, prime) == expected
                    checks += 1
    result = dict(status='EXACT_MODULAR_CACHE_CONTROLS_PASS', checks=checks,
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='Arithmetic optimization control on actual two-page rational columns at two primes; no new mathematical span claim.')
    (HERE/'overnight_upper_modular_cache.json').write_text(json.dumps(result, indent=2)+'\n')
    print(result, flush=True)


if __name__ == '__main__':
    main()
