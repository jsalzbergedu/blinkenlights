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

    def test_has_structure(self, obj):

    def test_basic_parse(self):
        response = blinkenlights.dispatch_command({"command": "parse", "filename": "test_data/4.1.c"}, self.con)
        pgm = response["node"]
        assert pgm >= 0
        response = blinkenlights.dispatch_command({"command": "get_kind", "idt": pgm}, self.con)
        assert response["kind"] == "pgm"
        response = blinkenlights.dispatch_command({"command": "get_child", "idt": pgm, "idx": 0}, self.con)
        return

    # Test pgm: select dest.id from node source inner join children on source.id=children.node left join node dest on children.child=dest.id where source.id=1;
    # select dest.* from node source inner join children on source.id=children.node AND children.idx=1 left join node dest on children.child=dest.id where source.id=1;


    @classmethod
    def teardown_class(cls):
        cls.con.close()
        return
