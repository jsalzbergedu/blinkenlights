"""
Tests for `blinkenlights` module.
"""
import pytest
from blinkenlights import blinkenlights


class TestBlinkenlights(object):

    @classmethod
    def setup_class(cls):
        cls.con = blinkenlights.setup_con()
        return

    def test_something(self):
        response = blinkenlights.dispatch_command({"command": "parse", "filename": "main.c"}, self.con)
        pgm = response["node"]
        assert pgm >= 0
        response = blinkenlights.dispatch_command({"command": "get_kind", "idt": pgm}, self.con)
        assert response["kind"] == "pgm"
        return
    # Test pgm: select dest.id from node source inner join children on source.id=children.node left join node dest on children.child=dest.id where source.id=1;
    # select dest.* from node source inner join children on source.id=children.node AND children.idx=1 left join node dest on children.child=dest.id where source.id=1;


    @classmethod
    def teardown_class(cls):
        cls.con.close()
        return
