/// <reference types="react" />
/**
 * Component that alerts if you click outside of it
 */
declare function OutsideAlerter(props: OutsideAlerterProps): JSX.Element;
interface OutsideAlerterProps {
    onClickOutside: () => void;
    children: any;
}
export default OutsideAlerter;
