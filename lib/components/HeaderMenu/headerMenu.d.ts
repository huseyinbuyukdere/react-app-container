/// <reference types="react" />
import { MenuItem } from '../../models';
interface HeaderMenuProps {
    itemList: MenuItem[];
}
declare const HeaderMenu: (props: HeaderMenuProps) => JSX.Element;
export default HeaderMenu;
