use Assert.assertEq

def mkSource(lines: List[String]): String =
    String.intercalate("\n", lines)

@Test
def parseAndTypeCheckAcceptsSimplePolymorphicDefinition(): Unit \ Assert = {
    let src = mkSource(
        "def id: forall a. a -> a \\ {} = \\x -> x" :: Nil
    );

    Assert.assertEq(
        expected = Ok(("id", Nil) :: Nil),
        Fresh.withFresh(() -> Parser.parseAndTypeCheck(src))
    )
}

@Test
def parseProgramAcceptsAssociatedEffectEqualitiesInsideInstances(): Unit \ Assert = {
    let src = mkSource(
        "trait Collect[a] {" ::
        "  type Elem" ::
        "  type Visit: Eff" ::
        "}" ::
        "instance Collect[List[a]] {" ::
        "  type Elem = a" ::
        "  type Visit: Eff = IO" ::
        "}" ::
        "def handler: Unit = ()" ::
        Nil
    );

    Assert.assertEq(
        expected = true,
        Result.isOk(Parser.parseProgram(src))
    )
}
