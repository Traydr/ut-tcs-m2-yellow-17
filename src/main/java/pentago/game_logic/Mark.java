package pentago.game_logic;

public enum Mark {
    EMPTY, BLACK, WHITE;

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
