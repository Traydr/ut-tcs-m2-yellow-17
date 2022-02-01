package pentago.client.player;

import pentago.game_logic.Mark;

public abstract class Player {
    private String name;
    private final Mark mark;
    private Strategy strategy;

    /**
     * Creates a new player object with a name and mark.
     *
     * @param name Name of the player
     * @param mark Mark of the player
     */
    /*@ requires name != null;
        requires mark == Mark.BLACK || mark == Mark.WHITE;
        ensures this.name == name;
        ensures this.mark == mark;
    @*/
    public Player(String name, Mark mark, Strategy strategy) {
        this.name = name;
        this.mark = mark;
        this.strategy = strategy;
    }

    public Player(String name, Mark mark) {
        this(name, mark, new NaiveStrategy());
    }

    /**
     * Returns the name of the player.
     *
     * @return Player name
     */
    public String getName() {
        return name;
    }

    /**
     * Updates the name of the player.
     *
     * @param name The new name of the player
     */
    public void setName(String name) {
        this.name = name;
    }

    /**
     * Returns the mark of the player.
     *
     * @return Player mark
     */
    public Mark getMark() {
        return mark;
    }

    /**
     * Returns the strategy of the bot.
     *
     * @return Strategy of the bot
     */
    public Strategy getStrategy() {
        return this.strategy;
    }
}
