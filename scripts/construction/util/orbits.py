"""Rotation orbits of sites modulo the period.

The rotation acts on a site by ``rho`` on its center, reduced into the period
square with the shift recorded, and leaves the radius unchanged. A family is
closed when every member's image is again a member with the same radius; the
conflict rule and the base then inherit that symmetry. A closed family is the
union of the orbits of its least members, so its orbit table, one row per
orbit holding that least member, records it completely: ``representatives``
reduces a family to that table and ``expand`` recovers the family from it.
"""

from __future__ import annotations

from collections.abc import Iterable
from typing import Optional

from .geometry import normalize, rotate
from .rationals import Site

__all__ = [
    'rotate_site',
    'orbit',
    'representative',
    'orbits',
    'closure_defect',
    'representatives',
    'expand',
    'canonical_defect',
]


def rotate_site(site: Site) -> tuple[Site, tuple[int, int]]:
    """Return the normalized rotated site and the shift z with rho(a) = a' + 59z."""
    s, t, radius = site
    rotated_s, rotated_t = rotate(s, t)
    image_s, shift_s = normalize(rotated_s)
    image_t, shift_t = normalize(rotated_t)
    return (image_s, image_t, radius), (shift_s, shift_t)


def orbit(site: Site) -> tuple[Site, ...]:
    """Return the distinct members of a site's rotation orbit, sorted."""
    members = set()
    current = site
    while current not in members:
        members.add(current)
        current, _ = rotate_site(current)
    return tuple(sorted(members))


def representative(site: Site) -> Site:
    """Return the least member of a site's orbit."""
    return orbit(site)[0]


def orbits(family: Iterable[Site]) -> dict[Site, tuple[Site, ...]]:
    """Group a family's sites by orbit representative, each group sorted."""
    groups: dict[Site, list[Site]] = {}
    for site in family:
        groups.setdefault(representative(site), []).append(site)
    return {key: tuple(sorted(group)) for key, group in groups.items()}


def closure_defect(family: Iterable[Site]) -> Optional[tuple[Site, Site]]:
    """Return the first site whose rotated image is absent, or None when closed."""
    members = set(family)
    for site in sorted(members):
        image, _ = rotate_site(site)
        if image not in members:
            return site, image
    return None


def representatives(family: Iterable[Site]) -> tuple[Site, ...]:
    """Return the orbit table of a family: the least member of each orbit, sorted."""
    return tuple(sorted({representative(site) for site in family}))


def expand(table: Iterable[Site]) -> tuple[Site, ...]:
    """Return the sorted union of the orbits of a table's sites, radii carried along."""
    members: set[Site] = set()
    for site in table:
        members.update(orbit(site))
    return tuple(sorted(members))


def canonical_defect(table: Iterable[Site]) -> Optional[Site]:
    """Return the first site that is not the least member of its orbit, or None.

    A table whose every row is the least member of its own orbit has one row
    per orbit, because an orbit has one least member.
    """
    for site in sorted(table):
        if representative(site) != site:
            return site
    return None
