package pentago.game_logic;

public enum Mark {
    EMPTY, BLACK, WHITE;

    /**
     * Overrides default toString() method.
     *
     * @return A string that represents the state of the board.
     * <p>
     * Could look something like this: ------------------------- |   | ○ |   | ● |   |   |
     * ------------------------- |   |   |   |   |   |   | ------------------------- |   |   |   | |
     *   |   | ------------------------- |   |   | ○ |   |   |   | ------------------------- |   | |
     * | ● |   |   | -------------------------
     */
    @Override
    public String toString() {
        switch (this) {
            case BLACK:
                return "○";
            case WHITE:
                return "●";
            default:
                return " ";
        }
    }
}
